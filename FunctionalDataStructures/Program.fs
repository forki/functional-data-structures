// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open CollectionsA.Hamt

open FSharpx.Collections
open System
open CollectionsA
open System.Collections.Generic

[<CustomEquality; CustomComparison>]
type KeyHash = KeyHash of int with
    override this.GetHashCode () = match this with KeyHash value -> value / 1

    interface IEquatable<KeyHash> with
        member this.Equals other = match this, other with KeyHash v1, KeyHash v2 -> v1 = v2

    interface IComparable<KeyHash> with
        member this.CompareTo other = match this, other with KeyHash v1, KeyHash v2 -> compare v1 v2

    interface IComparable with
        member this.CompareTo other = 
            match other with
            | :? KeyHash as keyHash -> (this :> IComparable<KeyHash>).CompareTo keyHash
            | _ -> failwith "weird"

    override this.Equals other = 
        match other with 
        | :? KeyHash as keyHash -> (this :> IEquatable<KeyHash>).Equals keyHash
        | _ -> false

[<EntryPoint>]
let main argv = 
    let n = 2000000
    let items = Seq.init n id

    let k = System.Diagnostics.Stopwatch.StartNew()

    //let h0 = 
    //    items
    //    |> Seq.fold (fun hamt item -> Hamt.add (KeyHash item) item hamt) Hamt.empty

    //printfn "%A %A" (Hamt.count h0) (k.ElapsedMilliseconds)

    //let p0 =
    //    items
    //    |> Seq.fold (fun hamt item -> PersistentHashMap.add (KeyHash item) item hamt) PersistentHashMap.empty

    //printfn "%A %A" (p0.Length) (k.ElapsedMilliseconds)

    //let m0 =
    //    items
    //    |> Seq.fold (fun map item -> Map.add (KeyHash item) item map) Map.empty

    //printfn "%A %A" (Map.count m0) (k.ElapsedMilliseconds)

    let d0 =
        items
        |> Seq.fold (fun (map: Dictionary<KeyHash, int>) item -> map.Add (KeyHash item, item); map ) (new Dictionary<KeyHash, int>())

    printfn "%A %A" (d0.Count) (k.ElapsedMilliseconds)

    0 // return an integer exit code1
