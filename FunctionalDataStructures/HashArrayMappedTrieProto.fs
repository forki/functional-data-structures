namespace Collections

module Array =

    let inline blit source sourceStart targetStart count target =
        if count > 0 then
            Array.blit source sourceStart target targetStart count
            target
        else
            target

    let inline set x index arr = 
        Array.set arr index x
        arr

    let insert x index arr =
        arr
        |> Array.length
        |> (+) 1
        |> Array.zeroCreate
        |> blit arr 0 0 index
        |> set x index
        |> blit arr (index + 1) (index + 1) (Array.length arr - index)

[<Measure>] type bit

type private Hash = int32

type private Bitmap = uint32

[<AutoOpen>]
module private Operators =

    let inline Bitmap (x: 'T) : Bitmap = uint32 x

    let inline Hash (x: 'T) : Hash = int32 x

    let inline asBits x = int x * 1<bit>

    let inline (<<<) bitmap (bits: int<bit>) = bitmap <<< (int bits)

    let inline (>>>) bitmap (bits: int<bit>) = bitmap >>> (int bits)

type private Node<'T> =
    | Leaf of 'T
    | Branch of Bitmap * Node<'T> array

module private Node =

    module private Helpers =

        let EMPTY_BITMAP = Bitmap 0

        let ZERO = EMPTY_BITMAP

        let ONE = Bitmap 1

        let FULL_BITMAP = ~~~EMPTY_BITMAP

        let MASK_COUNT_1 = Bitmap 0x55555555

        let MASK_COUNT_2 = Bitmap 0x33333333

        let MASK_COUNT_4 = Bitmap 0x0F0F0F0F

        let LAYER_BIT_COUNT = 5<bit>

        let LAYER_MASK = ~~~(FULL_BITMAP <<< LAYER_BIT_COUNT)

        let inline bit index = ONE <<< index

        let inline isBitOn bitmap index =
            bit index &&& bitmap <> EMPTY_BITMAP

        let inline keepLowerBitsOnly bitmap index =
            (bit index - ONE) &&& bitmap

        let bitOnCount bitmap =
            let a = bitmap - ((bitmap >>> 1<bit>) &&& MASK_COUNT_1)
            let b = (a &&& MASK_COUNT_2) + ((a >>> 2<bit>) &&& MASK_COUNT_2)
            ((((b + (b >>> 4<bit>)) &&& MASK_COUNT_4) * Bitmap 0x01010101) >>> 24<bit>)

        let inline setBit bitmap index = bitmap ||| (bit index)

    open Helpers

    let HASH_SIZE = 8<bit> * sizeof<Hash>

    let newBranch = Branch (EMPTY_BITMAP, Array.empty)

    let inline childBit key = asBits (Bitmap key &&& LAYER_MASK)

    let inline containsChild bitmap childBit =
        childBit
        |> isBitOn bitmap

    let inline childIndex bitmap childBit =
        childBit
        |> keepLowerBitsOnly bitmap
        |> bitOnCount
        |> int

    let inline setBit bitmap childBit =
        childBit
        |> setBit bitmap

    let inline nextLayerKey (currentKey, left) = let shift = min left LAYER_BIT_COUNT in (Hash (Bitmap currentKey >>> shift), left - shift)

    let rec add x node (key, left) =
        match node with
        | Leaf value -> Leaf x
        | Branch (bitmap, children) ->
            let childBit = childBit key
            let childRealIndex = childIndex bitmap childBit
            let nextLayerKey = nextLayerKey (key, left)
            if containsChild bitmap childBit then
                let newChild = add x children.[childRealIndex] nextLayerKey
                Branch (bitmap, children |> Array.copy |> Array.set newChild childRealIndex)
            elif snd nextLayerKey > 0<bit> then
                let newChild = add x newBranch nextLayerKey
                Branch (setBit bitmap childBit, children |> Array.insert newChild childRealIndex)
            else
                Branch (setBit bitmap childBit, children |> Array.insert (Leaf x) childRealIndex)

open Node

type Hamt<'K, 'T> = 
    private
    | Empty
    | Trie of Node<'T>

module Hamt =

    let empty() = Empty

    let add x hamt =
        match hamt with
        | Empty -> add x newBranch (hash x, HASH_SIZE)
        | Trie node -> add x node (hash x, HASH_SIZE)
        |> Trie