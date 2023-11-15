# tree_by_path

## Usage

In order to use this crate, add it to your project's Cargo.toml file using the command

```
cargo add tree_by_path
```

and add the below statement in your code :


```
use tree_by_path::{Node, PathError, TraverseAction};

```

## Trees are Nodes

```
pub struct Node<C> {
    pub cargo: C,
    pub children: Vec<Node<C>>,
}
```

tree_by_path trees consist of a `Node<C>` root node that may or may not have `Node<C>` children,
who in turn may or may not have other `Node<C>` children etc.

Every node carries a useful cargo of generic type C ("cargo"). (Nullability of the cargo can be
obtained by instantiating a tree having `Node<Option<YourType>>` nodes.)

Child nodes are directly owned by parent nodes as elements of their children vector :
`Vec<Node<C>>`.

Child nodes hold no reference to their parent. This parent, however, can always be retrieved by
removing the last element of the indexes array the node has been addressed with - see below.

This design has been chosen so as to avoid the use of `RefCell` or other inner mutability mechanisms, which defer borrow checking
from compilation to runtime.

## Address paths

Except for the root node, all nodes in the tree are an n-th element in their parent node's
children collection.

This means that every node can be addressed using a `Vec<usize>` series of indexes :
- the root node's address is an empty series of indexes : `[]`;
- any direct child node under the root node has one index in its address, starting with `[0]`;
- other nodes have a longer address, e.g.:

<pre>
 []
  |
 [0]-----------------[1]-----------------[2]
  |                   |
 [0,0]---[0,1]       [1,0]---[1,1]
          |                   |
         [0,1,0]             [1,1,0]---[1,1,1]---[1,1,2]
</pre>

These addresses are the paths meant in the crate's name.

Use of these addresses, which are `&Vec<usize>` objects accepted and returned by nearly all
methods of `struct Node<C>`, allow code using this crate to hold only one mutable reference to a
root node, without needing any other references, thus avoiding the need of holding on to
multiple mutable references of nodes of the same tree, which would be prohibited by Rust's
borrow checker.

So, instead of references to nodes, instances of `Vec<usize>` paths can be kept in variables.

And even if these path addresses can become obsolete after insertion or removal of nodes,
specific nodes can be retrieved by lookups on the nodes' cargo
using the `traverse*` methods if needed - see the section *Node identifiers* in the crate's documentation.

## Cloning
`Node<C>` is clonable if type `C` is clonable.

## Examples

*For usage examples, please see the crate's documentation or even the unit tests in src/lib.rs.*
