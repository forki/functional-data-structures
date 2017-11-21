module FDS.Core.ArithmeticHelpers

open FDS.Core.Units

let countBitsOn32 value =
    let a = value - ((rshift value 1<bit>) &&& 0x55555555u)
    let b = (a &&& 0x33333333u) + ((rshift a 2<bit>) &&& 0x33333333u)
    asBits (rshift (((b + (rshift b 4<bit>)) &&& 0x0F0F0F0Fu) * 0x01010101u) 24<bit>)

let countBitsOn64 (value: uint64) =
    let low = value |> uint32 |> countBitsOn32
    let high = rshift value 32<bit> |> uint32 |> countBitsOn32
    low + high