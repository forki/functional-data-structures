namespace CollectionsA

open BitwiseUnitsOfMeasure

[<Struct>]
type Bitmap = Bitmap of uint64 with
    static member inline (-) (Bitmap minuend, Bitmap subtrahend) = Bitmap (minuend - subtrahend)
    static member inline (<<<) ((Bitmap value), offset) = Bitmap (value <<< offset)
    static member inline (>>>) ((Bitmap value), offset) = Bitmap (value >>> offset)
    static member inline (&&&) (Bitmap left, Bitmap right) = Bitmap (left &&& right)
    static member inline (|||) (Bitmap left, Bitmap right) = Bitmap (left ||| right)

[<Struct>]
type Entry<'K, 'T> = Entry of key:'K * value:'T

type private Node<'K, 'T> =
    | Leaf of Entry<'K, 'T>
    | LeafWithCollisions of Entry<'K, 'T> list
    | Branch of Bitmap * Node<'K, 'T> array

[<Struct>]
type private Prefix = Prefix of bits: uint32 * length: int<bit>

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

    let inline prefixBits (Prefix (bits, _)) = bits

    let inline length (Prefix (_, length)) = length

module Bitmap =

    let inline ofValue value = uint64 value |> Bitmap

    let None: Bitmap = Bitmap 0UL

    let One: Bitmap = Bitmap 1UL

    let All: Bitmap = Bitmap 0xFFFF_FFFF_FFFF_FFFFUL

    [<Literal>]
    let LayerBitCount = 6<bit>

    let PrefixLayerMask = 0x3Fu

    let inline countBitsOn (Bitmap bitmap) = ArithmeticHelpers.countBitsOn64 bitmap

    let inline bit index = lshift One index

    let inline isBitOn index bitmap = bit index &&& bitmap <> None

    let inline onlyLowerBits index bitmap = (bit index - One) &&& bitmap

    let inline setBit index bitmap = bitmap ||| (bit index)

module Entry =

    let inline key (Entry (k, _)) = k

module private CollisionHelpers =
    open Prefix
    open Entry

    let collisionHash entries = entries |> List.head |> key |> hash
    
    let insertOrReplace entry entries =
        entries
        |> List.tryFindIndex (fun e -> key e = key entry)
        |> Option.map (fun index ->
            match List.splitAt index entries with
            | before, _::after -> before@entry::after
            | _ -> failwith "Never")
        |> Option.defaultWith (fun () -> entry::entries)

module private Node =
    open Prefix
    open Entry
    open CollisionHelpers

    let emptyBranch: Node<'K, 'T> = Branch (Bitmap.None, Array.empty)

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
            Leaf entry
        | Leaf oldEntry ->
            let oldHash = oldEntry |> key |> hash
            if entryHash = oldHash then
                LeafWithCollisions [ entry; oldEntry ]
            else
                let oldPrefix = currentLevelPrefixFromHash (length prefix) oldHash
                emptyBranch
                |> add oldEntry oldHash oldPrefix
                |> add entry entryHash prefix
        | LeafWithCollisions entries -> 
            let collisionHash = collisionHash entries
            if entryHash = collisionHash then
                LeafWithCollisions (insertOrReplace entry entries)
            else
                let collisionPrefix = currentLevelPrefixFromHash (length prefix) collisionHash
                let collisionBitIndex = childBitIndex collisionPrefix
                Branch (Bitmap.bit collisionBitIndex, [| node |])
                |> add entry entryHash prefix
        | Branch (bitmap, children) ->
            let bitIndex = childBitIndex prefix
            let arrayIndex = childArrayIndex bitIndex bitmap
            if containsChild bitIndex bitmap then
                let newChild = add entry entryHash (nextLayerPrefix prefix) children.[arrayIndex]
                Branch (bitmap, ArrayHelpers.put newChild arrayIndex children)
            else
                Branch (Bitmap.setBit bitIndex bitmap, ArrayHelpers.insert (Leaf entry) arrayIndex children)

type Hamt<'K, 'V> = 
    private
    | Empty 
    | Trie of Node<'K, 'V>

module Hamt =
    open Prefix

    let empty: Hamt<'K, 'V> = Empty

    let add key value = function
        | Empty -> Trie (Leaf (Entry (key, value)))
        | Trie root -> 
            let fullHash = hash key
            Node.add (Entry (key, value)) fullHash (Prefix (fullHash, HashSize)) root |> Trie
