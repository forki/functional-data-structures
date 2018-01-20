namespace FDS.Core

open FDS.Core.Units

[<Struct>]
type Bitmap<'T> = Bitmap of 'T with
    static member inline (<<<) ((Bitmap value), offset) = Bitmap (value <<< offset)
    static member inline (>>>) ((Bitmap value), offset) = Bitmap (value >>> offset)
    static member inline (&&&) (Bitmap left, Bitmap right) = Bitmap (left &&& right)
    static member inline (|||) (Bitmap left, Bitmap right) = Bitmap (left ||| right)
    static member inline (~~~) (Bitmap single) = Bitmap (~~~ single)

module Bitmap =

    let inline private (-) ((Bitmap minuend): Bitmap<'T>) ((Bitmap subtrahend): Bitmap<'T>): Bitmap<'T> = 
        Bitmap (minuend - subtrahend)

    let inline underlying< ^T, 'A when ^T: (static member Underlying: 'T -> 'A)> (v: 'T) =
        ((^T): (static member Underlying: 'T -> 'A) (v))

    let inline private unequal ((Bitmap a): Bitmap<'T>) ((Bitmap b): Bitmap<'T>) = underlying a <> underlying b

    let inline NoBit< ^T when ^T: (static member NoBit: unit -> ^T)> () =
        Bitmap ((^T): (static member NoBit: unit -> 'T) ())

    let inline FirstBit< ^T when ^T: (static member FirstBit: unit -> ^T)> () =
        Bitmap ((^T): (static member FirstBit: unit -> 'T) ())

    let inline AllBits< ^T when ^T: (static member FirstBit: unit -> ^T)> () =
        Bitmap ((^T): (static member FirstBit: unit -> 'T) ())

    let inline BitIndexBits< ^T when ^T: (static member BitIndexBits: unit -> int<bit>)> () =
        ((^T): (static member BitIndexBits: unit -> int<bit>) ())

    let inline BitIndexMask< ^T when ^T: (static member BitIndexMask: unit -> uint32)> () =
        ((^T): (static member BitIndexMask: unit -> uint32) ())

    let inline countBitsOn< ^T when ^T: (static member CountBitsOn: 'T -> int<bit>)> (Bitmap actualBits) =
        ((^T): (static member CountBitsOn: 'T -> int<bit>) (actualBits))

    let inline bit index = lshift (FirstBit ()) index

    let inline isBitOn index bitmap = unequal (bit index &&& bitmap) (NoBit ())

    let inline onlyLowerBits index bitmap = (bit index - FirstBit ()) &&& bitmap

    let inline setBit index bitmap = bitmap ||| (bit index)

    let inline clearBit index bitmap = bitmap &&& ~~~(bit index)


[<Struct>]
[<NoEquality>]
[<NoComparison>]
type UInt32W = UInt32W of uint32 with
    static member inline NoBit () = UInt32W (0u)
    static member inline FirstBit () = UInt32W (1u)
    static member inline CountBitsOn (UInt32W v) = ArithmeticHelpers.countBitsOn32 v
    static member inline BitIndexMask () = 0x1Fu
    static member inline BitIndexBits () = 5<bit>
    static member inline Underlying (UInt32W v) = v
    static member inline (-) (UInt32W minuend, UInt32W subtrahend) = UInt32W (minuend - subtrahend)
    static member inline (<<<) ((UInt32W value), offset) = UInt32W (value <<< offset)
    static member inline (>>>) ((UInt32W value), offset) = UInt32W (value >>> offset)
    static member inline (&&&) (UInt32W left, UInt32W right) = UInt32W (left &&& right)
    static member inline (|||) (UInt32W left, UInt32W right) = UInt32W (left ||| right)
    static member inline (~~~) (UInt32W single) = UInt32W (~~~ single)

[<Struct>]
[<NoEquality>]
[<NoComparison>]
type UInt64W = UInt64W of uint64 with
    static member inline NoBit () = UInt64W (0UL)
    static member inline FirstBit () = UInt64W (1UL)
    static member inline CountBitsOn (UInt64W v) = ArithmeticHelpers.countBitsOn64 v
    static member inline BitIndexMask () = 0x3Fu
    static member inline BitIndexBits () = 6<bit>
    static member inline Underlying (UInt64W v) = v
    static member inline (-) (UInt64W minuend, UInt64W subtrahend) = UInt64W (minuend - subtrahend)
    static member inline (<<<) ((UInt64W value), offset) = UInt64W (value <<< offset)
    static member inline (>>>) ((UInt64W value), offset) = UInt64W (value >>> offset)
    static member inline (&&&) (UInt64W left, UInt64W right) = UInt64W (left &&& right)
    static member inline (|||) (UInt64W left, UInt64W right) = UInt64W (left ||| right)
    static member inline (~~~) (UInt64W single) = UInt64W (~~~ single)