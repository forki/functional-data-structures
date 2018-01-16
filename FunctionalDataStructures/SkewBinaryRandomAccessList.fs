namespace rec CollectionsA

open System.Collections.Generic

type private Node<'T> =
    | Leaf of 'T
    | Branch of 'T * 'T Node * 'T Node

[<Struct>]
type private Root<'T> = Root of int * 'T Node

module private Node =

    let rec item index count = function
        | Leaf x when index = 0 -> x
        | Leaf _ -> failwith "Not enough elements"
        | Branch (x, _, _) when index = 0 -> x
        | Branch (_, left, _) when index <= count / 2 ->
            item (index - 1) (count / 2) left
        | Branch (_, _, right) ->
            item (index - 1 - count / 2) (count / 2) right
    
    let rec update value index count = function
        | Leaf _ when index = 0 -> Leaf value
        | Leaf _ -> failwith "Not enough elements"
        | Branch (_, left, right) when index = 0 -> Branch (value, left, right)
        | Branch (x, left, right) ->
            if index <= count / 2 then
                Branch (x, update value (index - 1) (count / 2) left, right)
            else
                Branch (x, left, update value (index - 1 - count /2) (count / 2) right)

    let rec toSeq node = 
        seq {
            match node with
            | Leaf x -> yield x
            | Branch (x, left, right) ->
                yield x
                yield! toSeq left
                yield! toSeq right}

    let rec foldBack node folder state =
        match node with
        | Leaf x -> folder x state
        | Branch (x, left, right) ->
            let newState =
                state
                |> foldBack right folder
                |> foldBack left folder
            folder x newState
            

module private NodeList =

    let rec private addAllFrom src dst =
        match src with
        | [] -> dst
        | x::xs -> addAllFrom xs (x::dst)

    let cons x = function
        | Root (w1, t1)::Root (w2, t2)::rest when w1 = w2 -> Root (1 + w1 + w2, Branch (x, t1, t2))::rest
        | list -> Root (1, Leaf x)::list

    let rec item index = function
        | Root (count, node)::_ when index < count -> Node.item index count node
        | Root (count, _)::rest -> item (index - count) rest
        | [] -> failwith "Not enough elements"

    let rec update value index prev = function
        | Root (count, node)::rest when index < count ->
            Root (count, Node.update value index count node)::rest
            |> addAllFrom prev
        | (Root (count, _) as x)::rest -> update value (index - count) (x::prev) rest
        | [] -> failwith "Not enough elements"

    let rec skip skipCount = function
        | any when skipCount <= 0 -> any
        | Root (count, Branch (_, left, right))::rest when skipCount < count / 2 + 1 ->
            skip (skipCount - 1) (Root (count / 2, left)::Root (count / 2, right)::rest)
        | Root (count, Branch (_, _, right))::rest when skipCount < count ->
            skip (skipCount - 1 - count / 2) (Root (count / 2, right)::rest)
        | Root (count, _)::rest -> skip (skipCount - count) rest
        | [] -> []

    let rec foldBack nodes folder state =
        match nodes with
        | Root (_, node)::rest ->
            state
            |> Node.foldBack node folder
            |> foldBack rest folder
        | [] -> state

    let rec skipAndFoldBack skipCount roots folder state = //a bit complex maybe
        if skipCount > 0 then
            match roots with
            | Root (count, _)::rest                          when skipCount >= count ->
                skipAndFoldBack 
                    (skipCount - count) 
                    rest 
                    folder 
                    state
            | Root (count, Branch (x, left, _))::rest        when skipCount >= count / 2 ->
                skipAndFoldBack 
                    (skipCount - count / 2) 
                    (Root (count / 2, left)::Root (1, Leaf x)::rest) 
                    folder 
                    state
            | Root (count, Branch (x, left, right))::rest ->
                skipAndFoldBack 
                    skipCount 
                    (Root (count / 2, right)::Root (count / 2, left)::Root (1, Leaf x)::rest) 
                    folder 
                    state
            | Root (_, Leaf _)::rest ->
                skipAndFoldBack 
                    (skipCount - 1) 
                    rest 
                    folder 
                    state
            | [] -> state
        else
            foldBack roots folder state

    let rec toSeq roots = 
        match roots with
        | [] -> Seq.empty
        | Root (_, node)::rest -> seq { yield! Node.toSeq node; yield! toSeq rest }

type SkewListVector<'T> = private SkewList of int * 'T Root list with

    interface IEnumerable<'T> with
        member this.GetEnumerator() = this |> SkewList.toSeq |> Enumerable.enumerator
        member this.GetEnumerator(): System.Collections.IEnumerator = 
            upcast (this |> SkewList.toSeq |> Enumerable.enumerator)

    member this.AsVector () = {
        new IEnumerable<'T> with
            member __.GetEnumerator(): IEnumerator<'T> = this |> SkewVector.toSeq |> Enumerable.enumerator
            member __.GetEnumerator(): System.Collections.IEnumerator = 
                upcast (this |> SkewVector.toSeq |> Enumerable.enumerator)  }
        
module SkewList =

    let empty: SkewListVector<'T> = SkewList (0, [])

    let singleton item = SkewList (1, [ Root (1, Leaf item) ]) 
    
    let cons x (SkewList (count, roots)) = SkewList (count + 1, NodeList.cons x roots)

    let count (SkewList (count, _)) = count

    let tryUncons (SkewList (count, roots)) = 
        match roots with
        | Root (_, Leaf x)::tail -> 
            Some (x, SkewList (count - 1, tail))
        | Root (w, Branch (x, t1, t2))::rest -> 
            Some (x, SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> 
            None

    let inline trySnoc list = tryUncons list

    let tryHead (SkewList (_, roots)) =
        match roots with
        | Root (_, Leaf x)::_ -> Some x
        | Root (_, Branch (x, _, _))::_ -> Some x
        | [] -> None

    let tryTail (SkewList (count, roots)) =
        match roots with
        | Root (_, Leaf _)::tail -> Some (SkewList (count - 1, tail))
        | Root (w, Branch (_, t1, t2))::rest -> Some (SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest)))
        | [] -> None

    let tryItem index (SkewList (count, roots)) =
        if index >= 0 && index < count 
            then NodeList.item index roots |> Some
            else None

    let tryUpdate index value (SkewList (count, roots)) =
        if index >= 0 && index < count
            then SkewList (count, NodeList.update value index [] roots) |> Some
            else None

    let trySkip skipCount (SkewList (count, roots)) =
        if skipCount >= 0 && skipCount <= count then
            SkewList (count - skipCount, NodeList.skip skipCount roots) |> Some
        else
            None

    let uncons (SkewList (count, roots)) = 
        match roots with
        | Root (_, Leaf x)::tail -> x, SkewList (count - 1, tail)
        | Root (w, Branch (x, t1, t2))::rest -> x, SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest)
        | [] -> failwith "Empty list"

    let inline snoc list = uncons list

    let head (SkewList (_, roots)) =
        match roots with
        | Root (_, Leaf x)::_ -> x
        | Root (_, Branch (x, _, _))::_ -> x
        | [] -> failwith "Empty list"

    let tail (SkewList (count, roots)) =
        match roots with
        | Root (_, Leaf _)::tail -> SkewList (count - 1, tail)
        | Root (w, Branch (_, t1, t2))::rest -> SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> failwith "Empty list"

    let item index (SkewList (count, roots)) =
        if index >= 0 && index < count 
            then NodeList.item index roots
            else failwith "Index out of bounds"

    let update index value (SkewList (count, roots)) =
        if index >= 0 && index < count 
            then SkewList (count, NodeList.update value index [] roots)
            else failwith "Index out of bounds"

    let skip skipCount (SkewList (count, roots)) =
        if skipCount >= 0 && skipCount <= count then
            SkewList (count - skipCount, NodeList.skip skipCount roots)
        else
            failwith "Can only skip 'n' elements where 0 <= 'n' <= count"

    let take takeCount (SkewList (count, roots)) =
        if takeCount >= 0 && takeCount <= count then
            SkewList (takeCount, NodeList.skipAndFoldBack (count - takeCount) roots NodeList.cons [])
        else
            failwith "Can only take 'n' elements where 0 <= 'n' <= count"

    let toSeq (SkewList (_, roots)) = NodeList.toSeq roots

    let ofSeq items = 
        items
        |> Seq.rev
        |> Seq.fold (fun list item -> cons item list) empty

    let (|Cons|EmptyList|) list =
        match trySnoc list with
        | Some pair -> Cons pair
        | None -> EmptyList

module private NodeAsVector =

    let rec toSeq node = 
        seq {
            match node with
            | Leaf x -> yield x
            | Branch (x, left, right) ->
                yield! toSeq right
                yield! toSeq left
                yield x}

module private NodeListAsVector =

    let rec toSeq roots = 
        match roots with
        | [] -> Seq.empty
        | Root (_, node)::rest -> seq { yield! toSeq rest; yield! NodeAsVector.toSeq node }

module SkewVector =

    let empty: SkewListVector<'T> = SkewList.empty

    let inline singleton item = SkewList.singleton item

    let inline conj x vector = SkewList.cons x vector

    let inline count vector = SkewList.count vector

    let tryUnconj (SkewList (count, roots)) = 
        match roots with
        | Root (_, Leaf x)::tail -> 
            Some (SkewList (count - 1, tail), x)
        | Root (w, Branch (x, t1, t2))::rest -> 
            Some (SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest), x)
        | [] -> 
            None

    let inline tryJnoc vector = tryUnconj vector

    let tryLast (SkewList (_, roots)) =
        match roots with
        | Root (_, Leaf x)::_ -> Some x
        | Root (_, Branch (x, _, _))::_ -> Some x
        | [] -> None

    let tryInitial (SkewList (count, roots)) =
        match roots with
        | Root (_, Leaf _)::tail -> Some (SkewList (count - 1, tail))
        | Root (w, Branch (_, t1, t2))::rest -> Some (SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest)))
        | [] -> None

    let inline tryItem index (SkewList (count, _) as vector) = SkewList.tryItem (count - index - 1) vector

    let inline tryUpdate index value (SkewList (count, _) as vector) = 
        SkewList.tryUpdate (count - index - 1) value vector

    let unconj (SkewList (count, roots)) = 
        match roots with
        | Root (_, Leaf x)::tail -> SkewList (count - 1, tail), x
        | Root (w, Branch (x, t1, t2))::rest -> SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest), x
        | [] -> failwith "Empty list"

    let inline jnoc vector = unconj vector

    let last (SkewList (_, roots)) =
        match roots with
        | Root (_, Leaf x)::_ -> x
        | Root (_, Branch (x, _, _))::_ -> x
        | [] -> failwith "Empty list"

    let initial (SkewList (count, roots)) =
        match roots with
        | Root (_, Leaf _)::tail -> SkewList (count - 1, tail)
        | Root (w, Branch (_, t1, t2))::rest -> SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> failwith "Empty list"

    let inline item index (SkewList (count, _) as vector) = SkewList.item (count - index - 1) vector

    let inline update index value (SkewList (count, _) as vector) = 
        SkewList.update (count - index - 1) value vector

    let inline skip skipCount (SkewList (count, _) as vector) =
        if skipCount >= 0 && skipCount <= count then
            SkewList.take (count - skipCount) vector
        else
            failwith "Can only skip 'n' elements where 0 <= 'n' <= count"

    let inline take takeCount (SkewList (count, _) as vector) =
        if takeCount >= 0 && takeCount <= count then
            SkewList.skip (count - takeCount) vector
        else
            failwith "Can only take 'n' elements where 0 <= 'n' <= count"

    let inline toSeq (SkewList (_, roots)) = NodeListAsVector.toSeq roots

    let inline ofSeq items = SkewList.ofSeq items

    let (|Conj|EmptyVector|) list =
        match tryJnoc list with
        | Some pair -> Conj pair
        | None -> EmptyVector