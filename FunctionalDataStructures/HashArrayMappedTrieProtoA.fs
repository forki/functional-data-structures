namespace CollectionsA

open BitwiseUnitsOfMeasure

[<Struct>]
type Bitmap = Bitmap of uint64 with
    static member inline (-) (Bitmap minuend, Bitmap subtrahend) = Bitmap (minuend - subtrahend)
    static member inline (<<<) ((Bitmap value), offset) = Bitmap (value <<< offset)
    static member inline (>>>) ((Bitmap value), offset) = Bitmap (value >>> offset)
    static member inline (&&&) (Bitmap left, Bitmap right) = Bitmap (left &&& right)
    static member inline (|||) (Bitmap left, Bitmap right) = Bitmap (left ||| right)
    static member inline (~~~) (Bitmap single) = Bitmap (~~~ single)

[<Struct>]
type Entry<'K, 'T> = Entry of key:'K * value:'T

type private Node<'K, 'T> =
    | Leaf of Entry<'K, 'T>
    | LeafWithCollisions of Entry<'K, 'T> list
    | Branch of Bitmap * Node<'K, 'T> array

[<Struct>]
type private Prefix = Prefix of bits: uint32 * length: int<bit>

type private AddOutcome = 
    | Added
    | Replaced

type private RemoveOutcome<'K, 'T> =
    | NothingLeft
    | Removed of Node<'K, 'T>
    | NotFound

module ArithmeticHelpers =

    let countBitsOn32 value =
        let a = value - ((rshift value 1<bit>) &&& 0x55555555u)
        let b = (a &&& 0x33333333u) + ((rshift a 2<bit>) &&& 0x33333333u)
        asBits (rshift (((b + (rshift b 4<bit>)) &&& 0x0F0F0F0Fu) * 0x01010101u) 24<bit>)

    let countBitsOn64 value =
        let low = value |> uint32 |> countBitsOn32
        let high = rshift value 32<bit> |> uint32 |> countBitsOn32
        low + high

module private Prefix =

    [<Literal>]
    let HashSize = 32<bit>

    let inline hash key = key |> hash |> uint32

    let inline currentLevelPrefixFromHash currentLength hash = Prefix (rshift hash (HashSize - currentLength), currentLength)

    let inline fullPrefixFromHash hash = currentLevelPrefixFromHash HashSize hash

    let inline prefixBits (Prefix (bits, _)) = bits

    let inline length (Prefix (_, length)) = length

module Bitmap =

    let inline ofValue value = uint64 value |> Bitmap

    let NoneSet: Bitmap = Bitmap 0UL

    let FirstSet: Bitmap = Bitmap 1UL

    let AllSet: Bitmap = Bitmap 0xFFFF_FFFF_FFFF_FFFFUL

    [<Literal>]
    let LayerBitCount = 6<bit>

    let PrefixLayerMask = 0x3Fu

    let inline countBitsOn (Bitmap bitmap) = ArithmeticHelpers.countBitsOn64 bitmap

    let inline bit index = lshift FirstSet index

    let inline isBitOn index bitmap = bit index &&& bitmap <> NoneSet

    let inline onlyLowerBits index bitmap = (bit index - FirstSet) &&& bitmap

    let inline setBit index bitmap = bitmap ||| (bit index)

    let inline clearBit index bitmap = bitmap &&& ~~~(bit index)

module Entry =

    let inline key (Entry (k, _)) = k

    let inline value (Entry (_, v)) = v

open Entry

module private CollisionHelpers =
    open Prefix
    open Entry

    let collisionHash entries = entries |> List.head |> key |> hash
    
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

    let emptyBranch: Node<'K, 'T> = Branch (NoneSet, Array.empty)

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
            let oldHash = oldEntry |> key |> hash
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
                Branch (Bitmap.bit collisionBitIndex, [| node |])
                |> add entry entryHash prefix
        | Branch (bitmap, children) ->
            let bitIndex = childBitIndex prefix
            let arrayIndex = childArrayIndex bitIndex bitmap
            if containsChild bitIndex bitmap then
                let (newChild, outcome) = add entry entryHash (nextLayerPrefix prefix) children.[arrayIndex]
                Branch (bitmap, ArrayHelpers.put newChild arrayIndex children), outcome
            else
                Branch (Bitmap.setBit bitIndex bitmap, ArrayHelpers.insert (Leaf entry) arrayIndex children), AddOutcome.Added

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
                tryFind targetKey targetHash (nextLayerPrefix prefix) children.[childArrayIndex bitIndex bitmap]
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
                match remove targetKey targetHash (nextLayerPrefix prefix) (Array.item childArrayIndex children) with
                | NotFound -> NotFound
                | Removed child -> Removed (Branch (bitmap, ArrayHelpers.put child childArrayIndex children))
                | NothingLeft ->
                    let newBitmap = clearBit bitIndex bitmap
                    if Array.isEmpty children
                        then NothingLeft
                    elif Array.length children = 1 
                        then Removed (Array.head children)
                    else
                        Removed (Branch (newBitmap, ArrayHelpers.remove childArrayIndex children))
            else
                NotFound             

type Hamt<'K, 'V> = 
    private
    | Empty 
    | Trie of root: Node<'K, 'V> * count: int

module Hamt =
    open Prefix

    let empty: Hamt<'K, 'V> = Empty

    let count = function
        | Empty -> 0
        | Trie (_, count) -> count

    let add key value = function
        | Empty -> Trie (Leaf (Entry (key, value)), 1)
        | Trie (root, count) -> 
            let hash = hash key
            match Node.add (Entry (key, value)) hash (fullPrefixFromHash hash) root with
            | newRoot, AddOutcome.Added -> Trie (newRoot, count + 1)
            | newRoot, AddOutcome.Replaced -> Trie (newRoot, count)

    let tryFind key = function
        | Empty -> None
        | Trie (root, _) ->
            let hash = hash key
            Node.tryFind key hash (fullPrefixFromHash hash) root

    let find key hamt =
        match tryFind key hamt with
        | Some value -> value
        | None -> failwith "Improve this exception"

