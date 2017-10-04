namespace Collections

[<Measure>] type bit

type private Hash = int32

type private Bitmap = uint32

[<AutoOpen>]
module private Operators =
    let inline (<<<) mask (bits: int<bit>) = mask <<< (int bits)

    let inline (>>>) mask (bits: int<bit>) = mask >>> (int bits)

    let inline bitmap x : Bitmap = uint32 x

type private Node<'T> =
    | Leaf of 'T
    | Branch of Bitmap * Node<'T> array

module private Node =

    let FULL_HASH_MASK: Bitmap = ~~~0u

    let HASH_SIZE = 8<bit> * sizeof<Hash>

    let LAYER_BIT_COUNT = 5<bit>

    let LAYER_MASK = ~~~(FULL_HASH_MASK <<< LAYER_BIT_COUNT)

    let inline childVirtualIndex key = key &&& LAYER_MASK

    let inline bit index = bitmap 1 <<< index

    let inline isBitOn bitmap index =
        bit index &&& bitmap <> 0u

    let inline keepLowerBitsOnly bitmap index =
        bit index - 1u &&& bitmap

    let bitOnCount (n: Bitmap) =
        let a = n - ((n >>> 1<bit>) &&& 0x55555555u)
        let b = (a & 0x33333333) + ((a >>> 2))
        1

    //let rec add x hash hashBits = 



type Hamt<'K, 'T> = 
    private
    | Empty
    | Trie of Node<'T>

module Hamt =

    let empty<'K, 'T> = Empty