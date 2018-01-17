namespace rec CollectionsA

open System.Collections.Generic

type private Node<'T> =
    | Leaf of 'T
    | Branch of 'T * 'T Node * 'T Node

[<Struct>]
type private Root<'T> = Root of int * 'T Node

exception private InvalidOperation of string

module private Node =

    let rec item index count = function
        | Leaf x when index = 0 -> x
        | Leaf _ -> raise (InvalidOperation "Not enough elements")
        | Branch (x, _, _) when index = 0 -> x
        | Branch (_, left, _) when index <= count / 2 ->
            item (index - 1) (count / 2) left
        | Branch (_, _, right) ->
            item (index - 1 - count / 2) (count / 2) right
    
    let rec update value index count = function
        | Leaf _ when index = 0 -> Leaf value
        | Leaf _ -> raise (InvalidOperation "Not enough elements")
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
        | [] -> raise (InvalidOperation "Not enough elements")

    let rec update value index prev = function
        | Root (count, node)::rest when index < count ->
            Root (count, Node.update value index count node)::rest
            |> addAllFrom prev
        | (Root (count, _) as x)::rest -> update value (index - count) (x::prev) rest
        | [] -> raise (InvalidOperation "Not enough elements")

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

type SkewListVector<'T> = private SkewListVector of int * 'T Root list with

    interface IEnumerable<'T> with
        member this.GetEnumerator() = this |> SkewList.toSeq |> Enumerable.enumerator
        member this.GetEnumerator(): System.Collections.IEnumerator = 
            upcast (this |> SkewList.toSeq |> Enumerable.enumerator)

    member this.AsVector () = {
        new IEnumerable<'T> with
            member __.GetEnumerator(): IEnumerator<'T> = this |> SkewVector.toSeq |> Enumerable.enumerator
            member __.GetEnumerator(): System.Collections.IEnumerator = 
                upcast (this |> SkewVector.toSeq |> Enumerable.enumerator)  }

exception EmptySkewCollection

exception IndexOutOfBounds of index: int * min: int * max: int

exception SkipOutOfBounds of value: int * maxSkip: int

exception TakeOutOfBounds of value: int * maxTake: int

module private SkewListProxy =
    
    let empty: SkewListVector<'T> = SkewListVector (0, [])

    let inline isEmpty (SkewListVector (count, _)) = count = 0

    let inline count (SkewListVector (count, _)) = count

    let singleton item = SkewListVector (1, [ Root (1, Leaf item) ]) 
    
    let cons x (SkewListVector (count, roots)) = SkewListVector (count + 1, NodeList.cons x roots)

    let snoc (SkewListVector (count, roots)) = 
        match roots with
        | Root (_, Leaf x)::tail -> x, SkewListVector (count - 1, tail)
        | Root (w, Branch (x, t1, t2))::rest -> x, SkewListVector (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest)
        | [] -> raise EmptySkewCollection

    let head (SkewListVector (_, roots)) =
        match roots with
        | Root (_, Leaf x)::_ -> x
        | Root (_, Branch (x, _, _))::_ -> x
        | [] -> raise EmptySkewCollection

    let tail (SkewListVector (count, roots)) =
        match roots with
        | Root (_, Leaf _)::tail -> SkewListVector (count - 1, tail)
        | Root (w, Branch (_, t1, t2))::rest -> SkewListVector (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> raise EmptySkewCollection

    let trySnoc (SkewListVector (count, roots)) = 
        match roots with
        | Root (_, Leaf x)::tail -> 
            Some (x, SkewListVector (count - 1, tail))
        | Root (w, Branch (x, t1, t2))::rest -> 
            Some (x, SkewListVector (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> 
            None

    let tryHead (SkewListVector (_, roots)) =
        match roots with
        | Root (_, Leaf x)::_ -> Some x
        | Root (_, Branch (x, _, _))::_ -> Some x
        | [] -> None

    let tryTail (SkewListVector (count, roots)) =
        match roots with
        | Root (_, Leaf _)::tail -> 
            Some (SkewListVector (count - 1, tail))
        | Root (w, Branch (_, t1, t2))::rest -> 
            Some (SkewListVector (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest)))
        | [] ->
            None

    let item index (SkewListVector (_, roots)) = NodeList.item index roots

    let update index value (SkewListVector (count, roots)) =
        SkewListVector (count, NodeList.update value index [] roots)

    let skip skipCount (SkewListVector (count, roots)) =
        SkewListVector (count - skipCount, NodeList.skip skipCount roots)

    let take takeCount (SkewListVector (count, roots)) =
        SkewListVector (takeCount, NodeList.skipAndFoldBack (count - takeCount) roots NodeList.cons [])

module SkewList =

    let empty: SkewListVector<'T> = SkewListProxy.empty

    let inline isEmpty list = SkewListProxy.isEmpty list

    let inline count list = SkewListProxy.count list

    let inline singleton item = SkewListProxy.singleton item
    
    let inline cons x list = SkewListProxy.cons x list

    let inline uncons list = SkewListProxy.snoc list

    let inline snoc list = SkewListProxy.snoc list

    let inline head list = SkewListProxy.head list

    let inline tail list = SkewListProxy.tail list

    let inline item index list =
        if index >= 0 && index < SkewListProxy.count list
            then SkewListProxy.item index list
            else raise (IndexOutOfBounds (index, 0, SkewListProxy.count list - 1))

    let inline update index value list =
        if index >= 0 && index < SkewListProxy.count list
            then SkewListProxy.update index value list
            else raise (IndexOutOfBounds (index, 0, SkewListProxy.count list - 1))

    let inline skip skipCount list =
        if skipCount >= 0 && skipCount <= SkewListProxy.count list
            then SkewListProxy.skip skipCount list
            else raise (SkipOutOfBounds (skipCount, SkewListProxy.count list))

    let inline take takeCount list =
        if takeCount >= 0 && takeCount <= SkewListProxy.count list
            then SkewListProxy.take takeCount list
            else raise (TakeOutOfBounds (takeCount, SkewListProxy.count list))

    let inline trySnoc list = SkewListProxy.trySnoc list

    let inline tryUncons list = trySnoc list

    let inline tryHead list =
        SkewListProxy.tryHead list

    let inline tryTail list =
        SkewListProxy.tryTail list

    let inline tryItem index list =
        if index >= 0 && index < SkewListProxy.count list
            then Some (SkewListProxy.item index list)
            else None

    let inline tryUpdate index value list =
        if index >= 0 && index < SkewListProxy.count list
            then Some (SkewListProxy.update index value list)
            else None

    let inline trySkip skipCount list =
        if skipCount >= 0 && skipCount <= SkewListProxy.count list
            then Some (SkewListProxy.skip skipCount list)
            else None

    let inline tryTake takeCount list =
        if takeCount >= 0 && takeCount <= SkewListProxy.count list
            then Some (SkewListProxy.take takeCount list)
            else None

    let inline toSeq (SkewListVector (_, roots)) = NodeList.toSeq roots

    let ofSeq items = 
        items
        |> Seq.rev
        |> Seq.fold (fun list item -> cons item list) empty

    let (|Cons|EmptyList|) list =
        if isEmpty list 
            then EmptyList
            else Cons (snoc list)

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

    let empty: SkewListVector<'T> = SkewListProxy.empty

    let inline isEmpty list = SkewListProxy.isEmpty list

    let inline count list = SkewListProxy.count list

    let inline singleton item = SkewListProxy.singleton item
    
    let inline conj x list = SkewListProxy.cons x list

    let inline unconj list = SkewListProxy.snoc list

    let inline jnoc list = SkewListProxy.snoc list

    let inline last list = SkewListProxy.head list

    let inline initial list = SkewListProxy.tail list

    let inline item index list =
        if index >= 0 && index < SkewListProxy.count list
            then SkewListProxy.item (SkewListProxy.count list - index - 1) list
            else raise (IndexOutOfBounds (index, 0, SkewListProxy.count list - 1))

    let inline update index value list =
        if index >= 0 && index < SkewListProxy.count list
            then SkewListProxy.update (SkewListProxy.count list - index - 1) value list
            else raise (IndexOutOfBounds (index, 0, SkewListProxy.count list - 1))

    let inline skip skipCount list =
        if skipCount >= 0 && skipCount <= SkewListProxy.count list
            then SkewListProxy.take (SkewListProxy.count list - skipCount) list
            else raise (SkipOutOfBounds (skipCount, SkewListProxy.count list))

    let inline take takeCount list =
        if takeCount >= 0 && takeCount <= SkewListProxy.count list
            then SkewListProxy.skip (SkewListProxy.count list - takeCount) list
            else raise (TakeOutOfBounds (takeCount, SkewListProxy.count list))

    let inline tryJnoc list = SkewListProxy.trySnoc list

    let inline tryUnconj list = tryJnoc list

    let inline tryHead list =
        SkewListProxy.tryHead list

    let inline tryTail list =
        SkewListProxy.tryTail list

    let inline tryItem index list =
        if index >= 0 && index < SkewListProxy.count list
            then Some (SkewListProxy.item index list)
            else None

    let inline tryUpdate index value list =
        if index >= 0 && index < SkewListProxy.count list
            then Some (SkewListProxy.update index value list)
            else None

    let inline trySkip skipCount list =
        if skipCount >= 0 && skipCount <= SkewListProxy.count list
            then Some (SkewListProxy.take (SkewListProxy.count list - skipCount) list)
            else None

    let inline tryTake takeCount list =
        if takeCount >= 0 && takeCount <= SkewListProxy.count list
            then Some (SkewListProxy.skip (SkewListProxy.count list - takeCount) list)
            else None

    let inline toSeq (SkewListVector (_, roots)) = NodeListAsVector.toSeq roots

    let inline ofSeq items = SkewList.ofSeq items

    let (|Conj|EmptyVector|) vector =
        if isEmpty vector
            then EmptyVector
            else Conj (jnoc vector)