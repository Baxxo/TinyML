// tree data type

// map function

// fold function

type 'a BinTree =

    // empty type, like leaf = Node(value, Empty, Empty)
    | Empty

    // node type, for every node of the tree
    // Node (value, leaf, Node(...))
    // Node (value, Node(...), Node(...))
    | Node of 'a * 'a BinTree * 'a BinTree


let rec map_tree tree func =
    match tree with
    | Empty -> Empty
    | Node (value, left, right) ->

        // apply func to the value
        let new_val = func value

        // apply to the left branch
        let new_left = map_tree left func

        // apply to the right branch
        let new_right = map_tree right func

        // return the new node
        Node (new_val, new_left, new_right)


let rec fold_tree tree func accu =
    | Empty -> accu
    | Node (value, left, right) ->

        // first fold left branch
        let accu_left = fold_tree (left, func, accu)

        // then accumulate in the new value the left accumulator with the value of the fold of right branch
        let accu_right = fold_tree (right, func, accu_left)

        // then return the value proccessed by the function passed by the user
        func (value, accu_right)