namespace rec CollectionsA

type private Node<'T> =
    | Leaf of 'T
    | Branch of 'T * 'T Node * 'T Node

[<Struct>]
type private Root<'T> = Root of int * 'T Node

module private Node =

    let cons x = function                                                                                              
        | Root (w1, t1)::Root (w2, t2)::rest when w1 = w2 -> Root (1 + w1 + w2, Branch (x, t1, t2))::rest
        | list -> Root (1, Leaf x)::list

    let rec private itemNode index count = function
        | Leaf x when index = 0 -> x
        | Leaf _ -> failwith "Not enough elements"
        | Branch (x, _, _) when index < 0 -> x
        | Branch (_, left, _) when index <= count / 2 ->
            itemNode (index - 1) (count / 2) left
        | Branch (_, _, right) ->
            itemNode (index - 1 - count / 2) (count / 2) right

    let rec item index = function
        | Root (count, node)::_ when index < count -> itemNode index count node
        | Root (count, _)::rest -> item (index - count) rest
        | [] -> failwith "Not enough elements"

    let rec private tryItemNode index count = function
        | Leaf x when index = 0 -> Some x
        | Leaf x -> None
        | Branch (x, _, _) when index < 0 -> Some x
        | Branch (_, left, _) when index <= count / 2 ->
            tryItemNode (index - 1) (count / 2) left
        | Branch (_, _, right) ->
            tryItemNode (index - 1 - count / 2) (count / 2) right

    let rec tryItem index = function
        | Root (count, node)::_ when index < count -> tryItemNode index count node
        | Root (count, _)::rest -> tryItem (index - count) rest
        | [] -> None

type SkewList<'T> = private SkewList of int * 'T Root list

module SkewList =
    
    let cons x (SkewList (count, nodes)) = SkewList (count + 1, Node.cons x nodes)

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
            then Node.item index nodes
            else failwith "Index out of bounds"

    let tryItem index (SkewList (count, nodes)) =
        if index >= 0 && index < count 
            then Node.tryItem index nodes
            else None