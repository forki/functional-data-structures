// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open Collections.Hamt

open FSharpx.Collections

[<EntryPoint>]
let main argv = 
    let h1 = empty()
    let h2 = add "abc" h1

    let p2 = 
        PersistentHashMap.empty 
        |> PersistentHashMap.add "abc1" "abc1"
        |> PersistentHashMap.add "abc2" "abc2"
        |> PersistentHashMap.add "abc3" "abc3"
    printfn "%A %A" h2 p2
    0 // return an integer exit code1
