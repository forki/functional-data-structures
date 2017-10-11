// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open CollectionsA.Hamt

open FSharpx.Collections
open System
open CollectionsA

[<CustomEquality>]
[<NoComparison>]
type KeyHash = KeyHash of int with
    override this.GetHashCode () = match this with KeyHash value -> value / 2

    interface IEquatable<KeyHash> with
        member this.Equals other = match this, other with KeyHash v1, KeyHash v2 -> v1 = v2

    override this.Equals other = 
        match other with 
        | :? KeyHash as keyHash -> (this :> IEquatable<KeyHash>).Equals keyHash
        | _ -> false

[<EntryPoint>]
let main argv = 
    let n = 2000000
    let items = Seq.init n id

    let k = System.Diagnostics.Stopwatch.StartNew()

    let h0 = 
        items
        |> Seq.fold (fun hamt item -> Hamt.add (KeyHash item) item hamt) Hamt.empty

    printfn "%A %A" (h0 = Hamt.empty) (k.ElapsedMilliseconds)

    //let p0 =
    //    items
    //    |> Seq.fold (fun hamt item -> PersistentHashMap.add (KeyHash item) item hamt) PersistentHashMap.empty

    //printfn "%A %A" (p0.Length) (k.ElapsedMilliseconds)

    0 // return an integer exit code1
