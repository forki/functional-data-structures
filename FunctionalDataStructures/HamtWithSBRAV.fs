namespace rec CollectionsB

open System.Collections.Generic
open FDS.Core
open FDS.Core.Units

[<Struct>]
type Entry<'K, 'T> = Entry of key:'K * value:'T

type private Node<'K, 'T> =
    | Leaf of Entry<'K, 'T>
    | LeafWithCollisions of Entry<'K, 'T> list
    | Branch of Bitmap * Node<'K, 'T> CollectionsC.SkewListVector

[<Struct>]
type private Prefix = Prefix of bits: uint32 * length: int<bit>

type private AddOutcome =
    | Added
    | Replaced

type private RemoveOutcome<'K, 'T> =
    | NothingLeft
    | Removed of Node<'K, 'T>
    | NotFound

module private Prefix =

    [<Literal>]
    let HashSize = 32<bit>

    let inline uhash key = key |> hash |> uint32

    let inline currentLevelPrefixFromHash currentLength hash = Prefix (rshift hash (HashSize - currentLength), currentLength)

    let inline fullPrefixFromHash hash = currentLevelPrefixFromHash HashSize hash

    let inline prefixBits (Prefix (bits, _)) = bits

    let inline length (Prefix (_, length)) = length

module Entry =

    let inline key (Entry (k, _)) = k

    let inline value (Entry (_, v)) = v

module private CollisionHelpers =
    open Prefix
    open Entry

    let collisionHash entries = entries |> List.head |> key |> uhash

    let insertOrReplace entry entries =
        entries
        |> List.tryFindIndex (fun e -> key e = key entry)
        |> Option.map (fun index ->
            match List.splitAt index entries with
            | before, _::after -> before@entry::after, AddOutcome.Replaced
            | _ -> failwith "Never")
        |> Option.defaultWith (fun () -> entry::entries, AddOutcome.Added)

    let removeIfExists targetKey entries =
        entries
        |> List.tryFindIndex (fun e -> key e = targetKey)
        |> Option.map (fun index ->
            match List.splitAt index entries with
            | before, _::after -> before@after
            | _ -> failwith "Never")
        |> Option.defaultValue entries

module private Node =

    open Prefix
    open Entry
    open CollisionHelpers
    open Bitmap
    open FDS.Core.Collections

    let insertSkewBRAV index value vector =
        let left = 
            vector
            |> CollectionsC.SkewVector.take index
            |> CollectionsC.SkewVector.conj value
        let right = CollectionsC.SkewVector.skip index vector
        CollectionsC.SkewVector.append left right

    let removeSkewBRAV index vector =
        let left = CollectionsC.SkewVector.take index vector
        let right = CollectionsC.SkewVector.skip (index + 1) vector
        CollectionsC.SkewVector.append left right

    let emptyBranch: Node<'K, 'T> = Branch (NoneSet, CollectionsC.SkewVector.empty)

    let inline childBitIndex prefix = (prefixBits prefix) &&& Bitmap.PrefixLayerMask |> asBits

    let inline containsChild childBitIndex bitmap = Bitmap.isBitOn childBitIndex bitmap

    let childArrayIndex childBitIndex bitmap =
        bitmap
        |> Bitmap.onlyLowerBits childBitIndex
        |> Bitmap.countBitsOn
        |> int

    let inline nextLayerPrefix (Prefix (bits, length)) =
        let shift = min length Bitmap.LayerBitCount
        Prefix (rshift bits shift, length - shift)

    let rec add entry entryHash prefix node =
        match node with
        | Leaf oldEntry when key entry = key oldEntry ->
            Leaf entry, AddOutcome.Replaced
        | Leaf oldEntry ->
            let oldHash = oldEntry |> key |> uhash
            if entryHash = oldHash then
                LeafWithCollisions [ entry; oldEntry ], AddOutcome.Added
            else
                let oldPrefix = currentLevelPrefixFromHash (length prefix) oldHash
                emptyBranch
                |> add oldEntry oldHash oldPrefix
                |> fst
                |> add entry entryHash prefix
        | LeafWithCollisions entries ->
            let collisionHash = collisionHash entries
            if entryHash = collisionHash then
                let (newEntries, outcome) = insertOrReplace entry entries
                LeafWithCollisions newEntries, outcome
            else
                let collisionPrefix = currentLevelPrefixFromHash (length prefix) collisionHash //aqui
                let collisionBitIndex = childBitIndex collisionPrefix
                Branch (Bitmap.bit collisionBitIndex, CollectionsC.SkewVector.singleton node)
                |> add entry entryHash prefix
        | Branch (bitmap, children) ->
            let bitIndex = childBitIndex prefix
            let arrayIndex = childArrayIndex bitIndex bitmap
            if containsChild bitIndex bitmap then
                let (newChild, outcome) = add entry entryHash (nextLayerPrefix prefix) (CollectionsC.SkewVector.item arrayIndex children)
                Branch (bitmap, CollectionsC.SkewVector.update arrayIndex newChild children), outcome
            else
                Branch (Bitmap.setBit bitIndex bitmap, insertSkewBRAV arrayIndex (Leaf entry) children), AddOutcome.Added

    let rec containsKey targetKey targetHash prefix = function
        | Leaf (Entry (key, _)) when key = targetKey -> true
        | Leaf _ -> false
        | LeafWithCollisions entries when collisionHash entries = targetHash ->
            List.exists (fun (Entry (key, _)) -> key = targetKey) entries
        | LeafWithCollisions _ -> false
        | Branch (bitmap, children) ->
            let bitIndex = childBitIndex prefix
            if containsChild bitIndex bitmap then
                containsKey targetKey targetHash (nextLayerPrefix prefix) (CollectionsC.SkewVector.item (childArrayIndex bitIndex bitmap) children)
            else
                false

    let rec tryFind targetKey targetHash prefix node =
        match node with
        | Leaf (Entry (key, value)) when key = targetKey ->
            Some value
        | Leaf _ -> None
        | LeafWithCollisions entries when collisionHash entries = targetHash ->
            List.tryFind (fun entry -> key entry = targetKey) entries |> Option.map value
        | LeafWithCollisions _ -> None
        | Branch (bitmap, children) ->
            let bitIndex = childBitIndex prefix
            if containsChild bitIndex bitmap then
                tryFind targetKey targetHash (nextLayerPrefix prefix) (CollectionsC.SkewVector.item (childArrayIndex bitIndex bitmap) children)
            else
                None

    let rec remove targetKey targetHash prefix node =
        match node with
        | Leaf (Entry (key, _)) when key = targetKey -> NothingLeft
        | Leaf _ -> NotFound
        | LeafWithCollisions entries when collisionHash entries = targetHash ->
            match removeIfExists targetKey entries with
            | newEntries when LanguagePrimitives.PhysicalEquality entries newEntries -> NotFound
            | [single] -> Removed (Leaf single)
            | moreThanOne -> Removed (LeafWithCollisions moreThanOne)
        | LeafWithCollisions _ -> NotFound
        | Branch (bitmap, children) ->
            let bitIndex = childBitIndex prefix
            if containsChild bitIndex bitmap then
                let childArrayIndex = childArrayIndex bitIndex bitmap
                match remove targetKey targetHash (nextLayerPrefix prefix) (CollectionsC.SkewVector.item childArrayIndex children) with
                | NotFound -> NotFound
                | Removed child -> Removed (Branch (bitmap, CollectionsC.SkewVector.update childArrayIndex child children))
                | NothingLeft ->
                    let newBitmap = clearBit bitIndex bitmap
                    if CollectionsC.SkewVector.isEmpty children
                        then NothingLeft
                    elif CollectionsC.SkewVector.count children = 1
                        then Removed (CollectionsC.SkewVector.last children)
                    else
                        Removed (Branch (newBitmap, removeSkewBRAV childArrayIndex children))
            else
                NotFound

    let rec toSeq = function
        | Leaf entry -> Seq.singleton entry
        | LeafWithCollisions entries -> upcast entries
        | Branch (_, children) -> Seq.collect toSeq children

    let rec keys = function
        | Leaf entry -> Seq.singleton (key entry)
        | LeafWithCollisions entries -> Seq.map key entries
        | Branch (_, children) -> Seq.collect keys children

type Hamt<'K, 'V> when 'K: equality =
    private
    | Empty
    | Trie of root: Node<'K, 'V> * count: int

    interface System.Collections.IEnumerable with
        member this.GetEnumerator() = upcast (this |> Hamt.toSeq |> CollectionsA.Enumerable.enumerator)

    interface IEnumerable<Entry<'K, 'V>> with
        member this.GetEnumerator() = this |> Hamt.toSeq |> CollectionsA.Enumerable.enumerator

    //interface IReadOnlyDictionary<'K, 'V> with
    //    member this.ContainsKey key = Hamt.containsKey key this
    //    member this.Count = Hamt.count this
    //    member this.GetEnumerator() = raise (System.NotImplementedException())
    //    member this.Item
    //        with get (key) = raise (System.NotImplementedException())
    //    member this.Keys = raise (System.NotImplementedException())
    //    member this.TryGetValue(key, value) = raise (System.NotImplementedException())
    //    member this.Values = raise (System.NotImplementedException())

module Hamt =
    open Prefix

    let empty: Hamt<'K, 'V> = Empty;

    let count = function
        | Empty -> 0
        | Trie (_, count) -> count

    let add key value = function
        | Empty -> Trie (Leaf (Entry (key, value)), 1)
        | Trie (root, count) ->
            let hash = uhash key
            match Node.add (Entry (key, value)) hash (fullPrefixFromHash hash) root with
            | newRoot, AddOutcome.Added -> Trie (newRoot, count + 1)
            | newRoot, AddOutcome.Replaced -> Trie (newRoot, count)

    let containsKey key = function
        | Empty -> false
        | Trie (root, _) ->
            let hash = uhash key;
            Node.containsKey key hash (fullPrefixFromHash hash) root

    let tryFind key = function
        | Empty -> None
        | Trie (root, _) ->
            let hash = uhash key
            Node.tryFind key hash (fullPrefixFromHash hash) root

    let find key hamt =
        match tryFind key hamt with
        | Some value -> value
        | None -> failwith "Improve this exception";

    let remove key hamt =
        match hamt with
        | Empty -> Empty
        | Trie (root, count) ->
            let hash = uhash key
            match Node.remove key hash (fullPrefixFromHash hash) root with
            | NotFound -> hamt
            | Removed node -> Trie (node, count - 1)
            | NothingLeft -> Empty

    let toSeq hamt =
        match hamt with
        | Empty -> Seq.empty
        | Trie (root, _) -> Node.toSeq root

    let keys hamt =
        match hamt with
        | Empty -> Seq.empty
        | Trie (root, _) -> Node.keys root

    let isEmpty hamt =
        match hamt with
        | Empty -> true
        | _ -> false