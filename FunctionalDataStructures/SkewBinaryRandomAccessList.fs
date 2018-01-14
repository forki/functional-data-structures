namespace rec CollectionsA

type private Node<'T> =
    | Leaf of 'T
    | Branch of 'T * 'T Node * 'T Node

[<Struct>]
type private Root<'T> = Root of int * 'T Node

module private Node =
    open System.Security.Cryptography.X509Certificates

    let rec item index count = function
        | Leaf x when index = 0 -> x
        | Leaf _ -> failwith "Not enough elements"
        | Branch (x, _, _) when index < 0 -> x
        | Branch (_, left, _) when index <= count / 2 ->
            item (index - 1) (count / 2) left
        | Branch (_, _, right) ->
            item (index - 1 - count / 2) (count / 2) right

    let rec tryItem index count = function
        | Leaf x when index = 0 -> Some x
        | Leaf _ -> None
        | Branch (x, _, _) when index < 0 -> Some x
        | Branch (_, left, _) when index <= count / 2 ->
            tryItem (index - 1) (count / 2) left
        | Branch (_, _, right) ->
            tryItem (index - 1 - count / 2) (count / 2) right

    let tryUpdate index value count node binder =
        let rec tryUpdate index count binder = function
            | Leaf _ when index = 0 -> binder (Leaf value)
            | Leaf _ -> None
            | Branch (_, left, right) when index < 0 -> binder (Branch (value, left, right))
            | Branch (x, left, right) -> 
                if index <= count / 2 then
                    tryUpdate (index - 1) (count / 2) (fun node -> binder (Branch (x, node, right))) left
                else
                    tryUpdate (index - 1 - count / 2) (count / 2) (fun node -> binder (Branch (x, left, node))) right
        tryUpdate index count binder node

    let rec toSeq node = 
        seq {
            match node with
            | Leaf x -> yield x
            | Branch (x, left, right) ->
                yield x
                yield! toSeq left
                yield! toSeq right}

module private NodeList =

    let cons x = function
        | Root (w1, t1)::Root (w2, t2)::rest when w1 = w2 -> Root (1 + w1 + w2, Branch (x, t1, t2))::rest
        | list -> Root (1, Leaf x)::list

    let rec item index = function
        | Root (count, node)::_ when index < count -> Node.item index count node
        | Root (count, _)::rest -> item (index - count) rest
        | [] -> failwith "Not enough elements"

    let rec tryItem index = function
        | Root (count, node)::_ when index < count -> Node.tryItem index count node
        | Root (count, _)::rest -> tryItem (index - count) rest
        | [] -> None

    let rec addAllFrom src dst =
        match src with
        | [] -> dst
        | x::xs -> addAllFrom xs (x::dst)

    let tryUpdate index value nodes binder =
        let rec tryUpdate index prev = function
            | Root (count, node)::rest when index < count -> 
                Node.tryUpdate index value count node (fun newNode -> 
                    Root (count, newNode)::rest
                    |> addAllFrom prev
                    |> binder)
            | (Root (count, _) as x)::rest -> tryUpdate (index - count) (x::prev) rest
            | [] -> None
        tryUpdate index [] nodes

    let rec toSeq nodes = 
        match nodes with
        | [] -> Seq.empty
        | Root (_, node)::rest -> seq { yield! Node.toSeq node; yield! toSeq rest }
        

type SkewListVector<'T> = private SkewList of int * 'T Root list

module SkewList =

    let empty: SkewListVector<'T> = SkewList (0, [])
    
    let cons x (SkewList (count, nodes)) = SkewList (count + 1, NodeList.cons x nodes)

    let count (SkewList (count, _)) = count

    let tryUncons (SkewList (count, nodes)) = 
        match nodes with
        | Root (_, Leaf x)::tail -> 
            Some (x, SkewList (count - 1, tail))
        | Root (w, Branch (x, t1, t2))::rest -> 
            Some (x, SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> 
            None

    let tryHead (SkewList (_, nodes)) =
        match nodes with
        | Root (_, Leaf x)::_ -> Some x
        | Root (_, Branch (x, _, _))::_ -> Some x
        | [] -> None

    let tryTail (SkewList (count, nodes)) =
        match nodes with
        | Root (_, Leaf _)::tail -> Some (SkewList (count - 1, tail))
        | Root (w, Branch (_, t1, t2))::rest -> Some (SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest)))
        | [] -> None

    let tryItem index (SkewList (count, nodes)) =
        if index >= 0 && index < count 
            then NodeList.tryItem index nodes
            else None

    let tryUpdate index value (SkewList (count, roots)) =
        if index >= 0 && index < count
            then NodeList.tryUpdate index value roots (fun newRoots -> SkewList (count, newRoots) |> Option.Some)
            else None

    let uncons (SkewList (count, nodes)) = 
        match nodes with
        | Root (_, Leaf x)::tail -> x, SkewList (count - 1, tail)
        | Root (w, Branch (x, t1, t2))::rest -> x, SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest)
        | [] -> failwith "Empty list"

    let head (SkewList (_, nodes)) =
        match nodes with
        | Root (_, Leaf x)::_ -> x
        | Root (_, Branch (x, _, _))::_ -> x
        | [] -> failwith "Empty list"

    let tail (SkewList (count, nodes)) =
        match nodes with
        | Root (_, Leaf _)::tail -> SkewList (count - 1, tail)
        | Root (w, Branch (_, t1, t2))::rest -> SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> failwith "Empty list"

    let item index (SkewList (count, nodes)) =
        if index >= 0 && index < count 
            then NodeList.item index nodes
            else failwith "Index out of bounds"

    let toSeq (SkewList (_, nodes)) = NodeList.toSeq nodes

    let ofSeq items = Seq.fold (fun list item -> cons item list) empty items

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

    let rec toSeq nodes = 
        match nodes with
        | [] -> Seq.empty
        | Root (_, node)::rest -> seq { yield! toSeq rest; yield! NodeAsVector.toSeq node }

module SkewVector =

    let empty: SkewListVector<'T> = SkewList.empty

    let inline conj x vector = SkewList.cons x vector

    let inline count vector = SkewList.count vector

    let tryUncon (SkewList (count, nodes)) = 
        match nodes with
        | Root (_, Leaf x)::tail -> 
            Some (SkewList (count - 1, tail), x)
        | Root (w, Branch (x, t1, t2))::rest -> 
            Some (SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest), x)
        | [] -> 
            None

    let tryLast (SkewList (_, nodes)) =
        match nodes with
        | Root (_, Leaf x)::_ -> Some x
        | Root (_, Branch (x, _, _))::_ -> Some x
        | [] -> None

    let tryInitial (SkewList (count, nodes)) =
        match nodes with
        | Root (_, Leaf _)::tail -> Some (SkewList (count - 1, tail))
        | Root (w, Branch (_, t1, t2))::rest -> Some (SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest)))
        | [] -> None

    let inline tryItem index (SkewList (count, _) as vector) = SkewList.tryItem (count - index - 1) vector

    let uncons (SkewList (count, nodes)) = 
        match nodes with
        | Root (_, Leaf x)::tail -> SkewList (count - 1, tail), x
        | Root (w, Branch (x, t1, t2))::rest -> SkewList (count - 1, Root (w / 2, t1)::Root (w / 2, t2)::rest), x
        | [] -> failwith "Empty list"

    let last (SkewList (_, nodes)) =
        match nodes with
        | Root (_, Leaf x)::_ -> x
        | Root (_, Branch (x, _, _))::_ -> x
        | [] -> failwith "Empty list"

    let initial (SkewList (count, nodes)) =
        match nodes with
        | Root (_, Leaf _)::tail -> SkewList (count - 1, tail)
        | Root (w, Branch (_, t1, t2))::rest -> SkewList (count - 1, (Root (w / 2, t1)::Root (w / 2, t2)::rest))
        | [] -> failwith "Empty list"

    let inline item index (SkewList (count, _) as vector) = SkewList.item (count - index - 1) vector

    let inline toSeq (SkewList (_, nodes)) = NodeListAsVector.toSeq nodes

    let inline ofSeq items = SkewList.ofSeq items