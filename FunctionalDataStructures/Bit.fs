namespace FDS.Core.Units

[<Measure>] type bit

[<AutoOpen>]
module BitOperators =

    let inline asBits value = int value * 1<bit>

    let inline lshift value (bits: int<bit>) = value <<< (int bits)

    let inline rshift value (bits: int<bit>) = value >>> (int bits)