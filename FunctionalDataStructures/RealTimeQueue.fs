namespace CollectionsE

open CollectionsF
open CollectionsF.Stream.ActivePattern

type 'T RTQueue = private { Front: 'T Stream; Back: 'T list; Schedule: 'T Stream } // |S| = |F| - |R|

module private Helpers =
    
    let rec private rotate f r acc =
        Stream.delayed <| fun _ ->
            match f, r with
            | Nil, [y] -> Stream.cons y acc
            | Cons (x, f'), y::r' -> Stream.cons x (rotate f' r' (Stream.cons y acc))
            | _ -> failwith "This should never happen"

    let rtQueue f r = function
        | Cons (x, s) -> { Front = f; Back = r; Schedule = s }
        | Nil -> let f' = rotate f r Stream.empty in { Front = f'; Back = []; Schedule = f' }

module RTQueue =

    let empty () = { Front = Stream.empty; Back = []; Schedule = Stream.empty }

    let isEmpty { Front = f } = Stream.isEmtpy f

    let snoc x { Front = f; Back = r; Schedule = s } = Helpers.rtQueue f (x::r) s

    let head { Front = f } =
        match f with
        | Cons (x, _) -> x
        | _ -> failwith "Empty queue"

    let tail { Front = f; Back = r; Schedule = s} =
        match f with
        | Cons (x, f') -> Helpers.rtQueue f' r s
        | _ -> failwith "Empty queue"