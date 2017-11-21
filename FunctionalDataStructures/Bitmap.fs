namespace FDS.Core

open FDS.Core.Units

[<Struct>]
type Bitmap = Bitmap of uint64 with
    static member inline (-) (Bitmap minuend, Bitmap subtrahend) = Bitmap (minuend - subtrahend)
    static member inline (<<<) ((Bitmap value), offset) = Bitmap (value <<< offset)
    static member inline (>>>) ((Bitmap value), offset) = Bitmap (value >>> offset)
    static member inline (&&&) (Bitmap left, Bitmap right) = Bitmap (left &&& right)
    static member inline (|||) (Bitmap left, Bitmap right) = Bitmap (left ||| right)
    static member inline (~~~) (Bitmap single) = Bitmap (~~~ single)

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