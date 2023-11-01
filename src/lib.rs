// TODO : change version to 1.1.0.
// TODO : add methods borrow_mut_cargo_(get_path_)by_id.
// TODO : add borrow_(mut_)node_(get_path_)by_id.
// TODO : add method extract_node_by_id
// TODO : add method has_id
// TODO : add method set_cargo_by_id
// TODO : rename fn traverse to fn traverse_mut and create a immutably traversing fn traverse.
//          And idem for traverse_back.
// TODO : Complete documentation about id-related structs and methods.

//{ Documentation
//! tree_by_path trees consist of a `Node<C>` root node that may or may not have `Node<C>` children,
//! who in turn may or may not have other `Node<C>` children etc.
//!
//! Every node carries a useful cargo of generic type C ("cargo"). (Nullability of the cargo can be
//! obtained by instantiating `Node<Option<Whatever>>` nodes.)
//!
//! Child nodes are directly owned by parent nodes as elements of their children vector :
//! `Vec<Node<C>>`.
//!
//! Child nodes hold no reference to their parent. This parent, however, can always be retrieved by
//! removing the last element of the indexes array the node has been addressed with - see below.
//!
//! ```
//! pub struct Node<C> {
//!     pub cargo: C,
//!     pub children: Vec<Node<C>>,
//! }
//! ```
//!
//! This design has been chosen so as to avoid the use of RefCell or other inner mutability mechanisms, which defer borrow checking
//! from compilation to runtime.
//!
//! Except for the root node, all nodes in the tree are an n-th element in their parent node's
//! children collection.
//!
//! This means that every node can be addressed using a `Vec<usize>` series of indexes :
//! - the root node's address is an empty series of indexes : `[]`;
//! - any direct child node under the root node has one index in its address, starting with `[0]`;
//! - other nodes have a longer address, e.g.:
//!
//!<pre>
//!   []
//!   |
//!   [0]---------------[1]--[2]
//!    |                 |
//!   [0,0]--[0,1]      [1,0]--[1,1]
//!            |                 |
//!          [0,1,0]           [1,1,0]--[1,1,1]--[1,1,2]
//!</pre>
//!
//! These addresses are the paths meant in the crate's name.
//!
//! Use of these addresses, which are `&Vec<usize>` objects accepted and returned by nearly all
//! methods of `struct Node<C>`, allow code using this crate to hold only one mutable reference to a
//! root node, without needing any other references, thus avoiding the need of holding on to
//! multiple mutable references of nodes of the same tree, which would be prohibited by Rust's
//! borrow checker.
//!
//! So, instead of references to nodes, instances of `Vec<usize>` paths can be kept in variables.
//!
//! And even if these path addresses can become obsolete after insertion or removal of nodes,
//! specific nodes can be retrieved by lookups using the `traverse*` methods if needed.
//!
//! # Cloning
//! `Node<C>` is clonable if type `C` is clonable :
//! ```
//! use tree_by_path::Node;
//! let n = Node::new(20u8);
//! let mut nc = n.clone();
//! let root_path = n.get_first_path();
//! let cloned_cargo = nc.borrow_mut_cargo(&root_path).unwrap();
//! *cloned_cargo = 21u8;
//! assert_eq!(&20u8, n.borrow_cargo(&root_path).unwrap());
//! assert_eq!(&21u8, nc.borrow_cargo(&root_path).unwrap());
//! ```
//!
//! Cloning a `Node<C>` instance having a non-clonable cargo, however, will cause a compilation error :
//! ```compile_fail
//! use tree_by_path::Node;
//!
//! #[derive(Debug)]
//! struct NoClone {}
//! 
//! let mut n = Node::new(NoClone{});
//! n.add_cargo_under(&Vec::<usize>::new(), NoClone{}).unwrap();
//! 
//! // The below statement doesn't even compile :
//! let nc = n.clone();
//! ```
//!
//! # Example :
//! ```
//! use tree_by_path::{Node, PathError, TraverseAction};
//!
//! let mut n = Node::new(0i8);
//! let mut result: Result<Vec<usize>, (PathError, i8)>;
//! let mut result_path: Vec<usize>;
//! 
//! // Adding a node with specified cargo after a node which doesn't exist yet :
//! result = n.add_cargo_after(&vec![0], 1);
//! assert!(result.is_err());
//! assert_eq!((PathError::RequestedPathNotAvailable, 1), result.unwrap_err());
//! 
//! // Now we create a node that will have address [0] :
//! result = n.add_cargo_under(&vec![], 1);
//! assert!(result.is_ok());
//! result_path = result.unwrap();
//! assert_eq!(vec![0], result_path);
//! 
//! // So now we can add a node after the one having address [0] :
//! result = n.add_cargo_after(&vec![0], 2);
//! assert!(result.is_ok());
//! result_path = result.unwrap();
//! assert_eq!(vec![1], result_path);
//! assert_eq!(&2, n.borrow_cargo(&result_path).unwrap());
//! 
//! result = n.add_cargo_after(&vec![0], 3);
//! assert!(result.is_ok());
//! result_path = result.unwrap();
//! assert_eq!(vec![1], result_path);
//! assert_eq!(&3, n.borrow_cargo(&result_path).unwrap());
//! assert_eq!(&2, n.borrow_cargo(&vec![2]).unwrap());
//!
//! // Traversing the cargoes of all nodes can be done using the iter() method :
//! let mut sum = n.iter().fold(
//!     0i8,
//!     |mut accum, &crg| {
//!         accum += crg;
//!         accum
//!     }
//! );
//!
//! assert_eq!(6i8, sum);
//!
//! // However, the traverse method runs somewhat faster and offers mutable access to the nodes :
//! n.traverse(
//!     0i8,
//!     |_acc, nd, _path| {
//!         nd.cargo *= 2i8;
//!         TraverseAction::Continue
//!     }
//! );
//!
//! assert_eq!(&4, n.borrow_cargo(&vec![2]).unwrap());
//!
//! sum = n.traverse(
//!     0i8,
//!     |acc, nd, _path| {
//!         *acc += nd.cargo;
//!         TraverseAction::Continue
//!     }
//! );
//!
//! assert_eq!(12i8, sum);
//!
//! ```
//}

use std::sync::atomic::{AtomicUsize, Ordering};

// { Documentation
/// The easiest way to construct a Node is by using its associated function Node::new, immediately
/// passing its cargo. As a tree consists of only Nodes, this first Node is a tree having one Node.
///
/// Afterwards, other Nodes can be added to the tree, either by passing a cargo, or else by
/// creating another Node (with or without subnodes) and adding it as a child to the first or any
/// other node of the tree :
/// ```
/// use tree_by_path::{Node, TraverseAction};
///
/// // Creating a first node.
/// let mut n = Node::new('a');
///
/// // n is a one-node tree now. Let's add a child node by passing a cargo.
/// let root_path = n.get_first_path();
/// n.add_cargo_under(&root_path, 'b').expect(
///     "It should always be possible to add a node under the root node");
///
/// // Let's create another small tree having cargoes of the same type.
/// let mut n2 = Node::new('c');
/// n2.add_cargo_under(&root_path, 'd').expect(
///     "It should always be possible to add a node under the root node");
///
/// // Now we add the second tree's root node as a child to the first tree's root node :
/// n.add_node_under(&root_path, n2).expect(
///     "It should always be possible to add a node under the root node");
///
/// // Concatenating all of the tree's nodes' cargoes :
/// let concatenated = n.traverse(
///     String::new(),
///     |accum, current_node, _path| {
///         accum.push(current_node.cargo);
///         TraverseAction::Continue
///     }
/// );
///
/// assert_eq!("abcd".to_string(), concatenated);
/// 
/// ```
// }
#[derive(Debug, PartialEq)]
pub struct Node<C> {
    pub cargo: C,
    pub children: Vec<Node<C>>,
}

impl<C> Node<C> {
    // { Documentation
    /// Creates a new node and immediately also a new tree having a single (root) node.
    ///
    /// The cargo has to be passed immediately. If you need a tree with optional cargoes
    /// in the nodes, create a node having an `Option<Whatever>` as cargo.
    ///
    /// Any node, with its subnodes, can  always be attached as a child to a node of a tree having nodes of the
    /// same cargo type. (See the `add_node_*` methods.)
    // }
    pub fn new(cargo: C) -> Node<C> {
        Node {
            cargo: cargo,
            children: Vec::<Node<C>>::new(),
        }
    }

    // { Documentation
    /// Returns `Vec::<usize>::new()`, as this is always the root node's path.
    // }
    pub fn get_first_path(&self) -> Vec<usize> {
        vec![]
    }

    // { Documentation
    /// Returns the path or address of the last subnode of the node on which this method is called.
    // }
    pub fn get_last_path(&self) -> Vec<usize> {
        let mut nd = self;
        let mut result_path = Vec::<usize>::new();
        let mut child_count: usize;

        loop {
            child_count = nd.children.len();

            if child_count == 0 {
                break;
            } else {
                child_count -= 1;
                nd = &nd.children[child_count];
                result_path.push(child_count);
            }
        }

        result_path
    }

    // { Documentation
    /// Returns the path or address of the next child node after the child node having the path passed as
    /// an argument.
    ///
    /// This next child node can be its first child, or its next sibling if it hasn't any children,
    /// or its parent's next sibling if it's the last child of its parent node, or even its
    /// grandparent, etc.
    ///
    /// If there is no next node (when the path passed as argument is the path of the tree's last
    /// node), a `PathError::RequestedPathNotAvailable` is returned.
    /// 
    /// Note that `Node.traverse` internally uses this method.
    ///
    /// Example :
    ///
    /// ```
    /// use tree_by_path::Node;
    ///
    /// let mut n = Node::new("Brussels".to_string());
    /// let root_path = Vec::<usize>::new();
    ///
    /// let ghent_path = n.add_cargo_under(&root_path, "Ghent".to_string()).expect(
    ///     "Error adding node under root node");
    ///
    /// let antwerp_path = n.add_cargo_under(&root_path, "Antwerp".to_string()).expect(
    ///     "Error adding node under root node");
    ///
    /// assert_eq!(Ok(antwerp_path.clone()), n.get_next_path(&ghent_path));
    /// ```
    // }
    pub fn get_next_path(&self, path: &Vec<usize>) -> Result<Vec<usize>, PathError> {
        let mut result_path = path.clone();

        match self.borrow_node(&result_path) {
            Err(err) => Err(err),
            Ok(nd) => {
                if nd.children.len() > 0 {
                    result_path.push(0);
                    Ok(result_path)
                } else {
                    // Repeat this logic in a loop in order to find the next sibling
                    // of the path node or of a parent that has one.

                    let mut next_node_index: usize;

                    loop {
                        if result_path.len() == 0 {
                            break Err(PathError::RequestedPathNotAvailable);
                        }

                        next_node_index = result_path.pop().unwrap() + 1;

                        match self.borrow_node(&result_path) {
                            Err(err) => break Err(err),
                            Ok(parent) => {
                                if next_node_index < parent.children.len() {
                                    result_path.push(next_node_index);
                                    break Ok(result_path);
                                }
                            },
                        }
                    }
                }
            },
        }
    }

    // { Documentation
    /// Returns the path or address of the previous child node before the child node having the path passed as
    /// an argument.
    ///
    /// If there is no previous node (when the path passed as argument is the path of the tree's
    /// first node), a `PathError::RequestedPathNotAvailable` is returned.
    ///
    /// Note that `Node.traverse_back` internally uses this method.
    // }
    pub fn get_previous_path(&self, path: &Vec<usize>) -> Result<Vec<usize>, PathError> {
        if path.len() == 0 {
            return Err(PathError::RequestedPathNotAvailable);
        }

        let mut result_path = path.clone();

        match self.borrow_node(&result_path) {
            Err(err) => Err(err),
            Ok(_) => {
                let input_index = result_path.pop().unwrap();
                let mut children_count: usize;

                if input_index > 0 {
                    result_path.push(input_index - 1);

                    // Descend do deepest last grandchild of this node.
                    loop {
                        match self.borrow_node(&result_path) {
                            Err(err) => break Err(err),
                            Ok(nd) => {
                                    children_count = nd.children.len();

                                    if children_count > 0 {
                                        result_path.push(children_count -1);
                                    } else {
                                        break Ok(result_path);
                                    }
                            },
                        }
                    }
                } else  {
                    // Return parent's path.
                    Ok(result_path)
                }
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// adds a new child node under it having the given cargo,<br />
    /// and returns a Result being either<br />
    /// `   Ok(path_of_added_node)`<br />
    /// or else<br />
    /// `   Err((PathError, cargo_not_having_been_moved_into_tree))`.
    ///
    /// Example :
    /// ```
    /// use tree_by_path::{Node, PathError};
    ///
    /// let mut n = Node::new(0u8);
    /// let mut result: Result<Vec<usize>, (PathError, u8)>;
    ///
    /// result = n.add_cargo_under(&vec![], 1);
    /// assert!(result.is_ok());
    /// assert_eq!(vec![0], result.unwrap());
    ///
    /// result = n.add_cargo_under(&vec![], 2);
    /// assert!(result.is_ok());
    /// assert_eq!(vec![1], result.unwrap());
    /// assert_eq!(&2, n.borrow_cargo(&vec![1]).unwrap());
    ///
    /// result = n.add_cargo_under(&vec![0], 3);
    /// assert!(result.is_ok());
    /// assert_eq!(vec![0, 0], result.unwrap());
    ///
    /// result = n.add_cargo_under(&vec![0], 4);
    /// assert!(result.is_ok());
    /// assert_eq!(vec![0, 1], result.unwrap());
    ///
    /// let borrowed = n.borrow_cargo(&vec![0, 1]);
    /// assert!(borrowed.is_ok());
    /// assert_eq!(&4, borrowed.unwrap());
    ///
    /// result = n.add_cargo_under(&vec![50], 99);
    /// assert!(result.is_err());
    /// assert_eq!((PathError::InputPathNotFound,99), result.unwrap_err());
    ///
    /// result = n.add_cargo_under(&vec![0, 1, 1], 99);
    /// assert!(result.is_err());
    /// assert_eq!((PathError::InputPathNotFound,99), result.unwrap_err());
    /// ```
    // }
    pub fn add_cargo_under(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, (PathError, C)> {
        let mut result_path = path.clone();
        let borrowed = self.borrow_mut_node(path);

        match borrowed {
            Err(err) => Err((err, cargo)),
            Ok(nd) =>  {
                let ix = nd.children.len();
                result_path.push(ix);
                nd.children.push(Node::new(cargo));

                Ok(result_path)
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// adds a new child node after it,<br />
    /// and returns a Result being either<br />
    /// `   Ok(path_of_added_node)`<br />
    /// or else<br />
    /// `   Err((PathError, cargo_not_having_been_moved_into_tree))`.
    ///
    /// Note that trying to add a node after the root node cannot but result in<br />
    /// `Err((PathError::InputPathNotFitForOperation, cargo_not_having_been_moved_into_tree))`,<br />
    /// as a tree's root node can't have siblings.
    // }
    pub fn add_cargo_after(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, (PathError, C)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, cargo));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap() + 1;

        let borrowed = self.borrow_mut_node(&result_path);

        match borrowed {
            Err(err) => Err((err, cargo)),
            Ok(nd) =>  {
                if last_path > nd.children.len() {
                    Err((PathError::RequestedPathNotAvailable, cargo))
                } else {
                    nd.children.insert(last_path, Node::new(cargo));
                    result_path.push(last_path);

                    Ok(result_path)
                }
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// adds a new child node before it,<br />
    /// and returns a Result being either<br />
    /// `   Ok(path_of_added_node)`<br />
    /// or else<br />
    /// `   Err((PathError, cargo_not_having_been_moved_into_tree))`.
    ///
    /// Note that trying to add a node before the root node cannot but result in<br />
    /// `Err((PathError::InputPathNotFitForOperation, cargo_not_having_been_moved_into_tree))`,<br />
    /// as a tree's root node can't have siblings.
    // }
    pub fn add_cargo_before(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, (PathError, C)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, cargo));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap();

        let borrowed = self.borrow_mut_node(&result_path);

        match borrowed {
            Err(err) => Err((err, cargo)),
            Ok(nd) =>  {
                if last_path > nd.children.len() {
                    Err((PathError::InputPathNotFound, cargo))
                } else {
                    nd.children.insert(last_path, Node::new(cargo));
                    result_path.push(last_path);

                    Ok(result_path)
                }
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// tries and removes it<br />
    /// and returns either<br />
    /// `   Ok(removed_node_with_all_its_children)`<br />
    /// or<br />
    /// `   Err(PathError)`.
    ///
    /// Trying and removing the root node amounts to trying and removing a node from itself, which
    /// cannot but result in an `Err(PathError::InputPathNotFitForOperation)`:
    ///
    /// ```
    /// use tree_by_path::{Node, PathError};
    ///
    /// let mut n = Node::new(("Jane Kirby", "CEO"));
    /// let root_path = n.get_first_path();
    ///
    /// let cfo_path = n.add_cargo_under(
    ///     &root_path,
    ///     ("Rob Delsing", "CFO")
    /// ).unwrap();
    ///
    /// let account_path = n.add_cargo_under(
    ///     &cfo_path,
    ///     ("Pierre Lévèque", "Head of Accounting")
    /// ).unwrap();
    ///
    /// let cio_path = n.add_cargo_under(
    ///     &root_path,
    ///     ("Dilshat Ahmetova", "CFO")
    /// ).unwrap();
    ///
    /// let mut result = n.extract_node(&root_path);
    /// assert_eq!(Err(PathError::InputPathNotFitForOperation), result);
    ///
    /// result = n.extract_node(&cfo_path);
    /// match result {
    ///     Err(_) => panic!("Failed to extract an existing child node."),
    ///     Ok(cfo_tree) => {
    ///         assert_eq!("Pierre Lévèque", cfo_tree.borrow_cargo(&vec![0]).unwrap().0)
    ///     },
    /// }
    ///
    /// assert_eq!("Dilshat Ahmetova", n.borrow_cargo(&vec![0]).unwrap().0)
    /// ```
    // }
    pub fn extract_node(&mut self, path: &Vec<usize>) -> Result<Node<C>, PathError> {
        if path.len() == 0 {
            return Err(PathError::InputPathNotFitForOperation);
        }

        let mut parent_path = path.clone();
        let last_index = parent_path.pop().unwrap();
        let parent_result = self.borrow_mut_node(&parent_path);

        match parent_result {
            Err(err) => Err(err),
            Ok(parent) => {
                if parent.children.len() <= last_index {
                    Err(PathError::InputPathNotFound)
                } else {
                    Ok(parent.children.remove(last_index))
                }
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// adds the given node under it,<br />
    /// and returns a Result being either<br />
    /// `   Ok(path_of_added_node)`<br />
    /// or else<br />
    /// `   Err((PathError, node_not_having_been_moved_into_tree))`.
    ///
    /// Example :
    /// ```
    /// use tree_by_path::{Node, PathError};
    ///
    /// let mut n = Node::new(0u8);
    /// let mut result: Result<Vec<usize>, (PathError, Node<u8>)>;
    ///
    /// result = n.add_node_under(&vec![], Node::new(1));
    /// assert!(result.is_ok());
    /// assert_eq!(vec![0], result.unwrap());
    ///
    /// result = n.add_node_under(&vec![], Node::new(2));
    /// assert!(result.is_ok());
    /// assert_eq!(vec![1], result.unwrap());
    /// assert_eq!(&2, n.borrow_cargo(&vec![1]).unwrap());
    ///
    /// result = n.add_node_under(&vec![0], Node::new(3));
    /// assert!(result.is_ok());
    /// assert_eq!(vec![0, 0], result.unwrap());
    ///
    /// result = n.add_node_under(&vec![0], Node::new(4));
    /// assert!(result.is_ok());
    /// assert_eq!(vec![0, 1], result.unwrap());
    ///
    /// let borrowed = n.borrow_cargo(&vec![0, 1]);
    /// assert!(borrowed.is_ok());
    /// assert_eq!(&4, borrowed.unwrap());
    ///
    /// result = n.add_node_under(&vec![50], Node::new(99));
    /// assert!(result.is_err());
    /// assert_eq!((PathError::InputPathNotFound, Node::new(99)), result.unwrap_err());
    ///
    /// result = n.add_node_under(&vec![0, 1, 1], Node::new(99));
    /// assert!(result.is_err());
    /// assert_eq!((PathError::InputPathNotFound, Node::new(99)), result.unwrap_err());
    /// ```
    // }
    pub fn add_node_under(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Vec<usize>, (PathError, Node<C>)> {
        let mut result_path = path.clone();
        let borrowed = self.borrow_mut_node(path);

        match borrowed {
            Err(err) => Err((err, node)),
            Ok(nd) =>  {
                let ix = nd.children.len();
                result_path.push(ix);
                nd.children.push(node);

                Ok(result_path)
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// adds the given node after it,<br />
    /// and returns a Result being either<br />
    /// `   Ok(path_of_added_node)`<br />
    /// or else<br />
    /// `   Err((PathError, node_not_having_been_moved_into_tree))`.
    ///
    /// Note that trying to add a node after the root node cannot but result in<br />
    /// `Err((PathError::InputPathNotFitForOperation, node_not_having_been_moved_into_tree))`,<br />
    /// as a tree's root node can't have siblings.
    // }
    pub fn add_node_after(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Vec<usize>, (PathError, Node<C>)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, node));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap() + 1;

        let borrowed = self.borrow_mut_node(&result_path);

        match borrowed {
            Err(err) => Err((err, node)),
            Ok(nd) =>  {
                if last_path > nd.children.len() {
                    Err((PathError::RequestedPathNotAvailable, node))
                } else {
                    nd.children.insert(last_path, node);
                    result_path.push(last_path);

                    Ok(result_path)
                }
            },
        }
    }

    // { Documentation
    /// Looks for the tree's child node having the given path,<br />
    /// adds the given node before it,<br />
    /// and returns a Result being either<br />
    /// `   Ok(path_of_added_node)`<br />
    /// or else<br />
    /// `   Err((PathError, node_not_having_been_moved_into_tree))`.
    ///
    /// Note that trying to add a node before the root node cannot but result in<br />
    /// `Err((PathError::InputPathNotFitForOperation, node_not_having_been_moved_into_tree))`,<br />
    /// as a tree's root node can't have siblings.
    // }
    pub fn add_node_before(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Vec<usize>, (PathError, Node<C>)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, node));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap();

        let borrowed = self.borrow_mut_node(&result_path);

        match borrowed {
            Err(err) => Err((err, node)),
            Ok(nd) =>  {
                if last_path > nd.children.len() {
                    Err((PathError::InputPathNotFound, node))
                } else {
                    nd.children.insert(last_path, node);
                    result_path.push(last_path);

                    Ok(result_path)
                }
            },
        }
    }

    // { Documentation
    /// Looks for the node having the given path,<br />
    /// replaces it (with all its child nodes !) by the given node (with all its child nodes),<br />
    /// and returns either<br />
    /// `   Ok(node_that_was_replaced)`<br />
    /// or else<br />
    /// `   Err((PathError, node_not_having_been_moved_into_tree)`.
    ///
    /// Note that trying and replacing the root node will result in a<br />
    /// `Err((PathError::InputPathNotFitForOperation, node))`.
    ///
    /// But even if replacing a tree's child node is not possible, it is possible to replace its
    /// cargo.
    // }
    pub fn swap_node(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Node<C>, (PathError, Node<C>)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, node));
        }

        let mut parent_path = path.clone();
        let last_path = parent_path.pop().unwrap();

        let borrowed = self.borrow_mut_node(&parent_path);

        match borrowed {
            Err(err) => Err((err, node)),
            Ok(nd) =>  {
                if last_path >= nd.children.len() {
                    Err((PathError::InputPathNotFound, node))
                } else {
                    let removed_node = nd.children.remove(last_path);
                    nd.children.insert(last_path, node);

                    Ok(removed_node)
                }
            },
        }
    }

    // { Documentation
    /// Returns a `Result` having either
    /// - a non-mutable reference to the cargo of the child node having the given path<br />
    /// or else
    /// - a `PathError`.
    ///
    /// Example:
    /// ```
    /// use tree_by_path::Node;
    ///
    /// let mut n = Node::new("Athens");
    /// let root_path = Vec::<usize>::new();
    /// let mut added_path: Vec<usize>;
    ///
    /// added_path = n.add_cargo_under(&root_path, "Thessaloniki").unwrap();
    /// added_path = n.add_cargo_under(&added_path, "Kilkis").unwrap();
    ///
    /// added_path = n.add_cargo_under(&root_path, "Kavala").unwrap();
    /// added_path = n.add_cargo_under(&added_path, "Moustheni").unwrap();
    ///
    /// let borrow_result = n.borrow_cargo(&vec![1, 0]);
    ///
    /// assert!(borrow_result.is_ok());
    /// assert_eq!(&"Moustheni", borrow_result.unwrap());
    /// ```
    // }
    pub fn borrow_cargo(&self, path: &Vec<usize>) -> Result<&C, PathError> {
        let borrowed = self.borrow_node(path);

        match borrowed {
            Ok(nd) => Ok(&nd.cargo),
            Err(err) => Err(err),
        }
    }

    // { Documentation
    /// Returns a `Result` having either
    /// - a mutable reference to the cargo of the child node having the given path<br />
    /// or else
    /// - a `PathError`.
    ///
    /// Note : an easier way to change a (child) node's cargo is the set_cargo method.
    ///
    /// Example:
    /// ```
    /// use tree_by_path::Node;
    ///
    /// let mut n = Node::new("Greece");
    /// let root_path = Vec::<usize>::new();
    /// let mut added_path: Vec<usize>;
    ///
    /// added_path = n.add_cargo_under(&root_path, "Thessaloniki").unwrap();
    /// added_path = n.add_cargo_under(&added_path, "Kilkis").unwrap();
    ///
    /// added_path = n.add_cargo_under(&root_path, "Kavala").unwrap();
    /// added_path = n.add_cargo_under(&added_path, "Moustheni").unwrap();
    ///
    /// let mut borrow_result = n.borrow_mut_cargo(&vec![1, 0]);
    /// assert!(borrow_result.is_ok());
    /// let borrowed = borrow_result.unwrap();
    ///
    /// *borrowed = "Kokkinochori";
    /// 
    /// borrow_result = n.borrow_mut_cargo(&vec![1, 0]);
    /// assert!(borrow_result.is_ok());
    /// assert_eq!(&"Kokkinochori", borrow_result.unwrap());
    /// ```
    // }
    pub fn borrow_mut_cargo(&mut self, path: &Vec<usize>) -> Result<&mut C, PathError> {
        let borrowed = self.borrow_mut_node(path);

        match borrowed {
            Ok(nd) => Ok(&mut nd.cargo),
            Err(err) => Err(err),
        }
    }

    // { Documentation
    /// Returns a `Result` having either
    /// - ()<br />
    /// or else
    /// - a tuple `(PathError, cargo_not_having_been_moved_into_the_tree)`.
    ///
    /// Note that the cargo previously held by the targeted node is lost after a call to `set_cargo`.
    /// In order to retrieve the previously held cargo, use the `swap_cargo` method which, however, is a more
    /// expensive operation.
    ///
    /// Example:
    /// ```
    /// use tree_by_path::Node;
    ///
    /// let mut n = Node::new('a');
    /// n.add_cargo_under(&vec![], 'b').unwrap();
    /// n.add_cargo_under(&vec![], 'c').unwrap();
    ///
    /// let result = n.set_cargo(&vec![1], 'z');
    ///
    /// assert!(result.is_ok());
    /// assert_eq!(&'z', n.borrow_cargo(&vec![1]).unwrap());
    /// ```
    // }
    pub fn set_cargo(&mut self, path: &Vec<usize>, cargo: C) -> Result<(), (PathError, C)> {
        match self.borrow_mut_cargo(path) {
            Ok(borrowed_cargo) => {
                *borrowed_cargo = cargo;
                Ok(())
            },
            Err(err) => Err((err, cargo)),
        }
    }

    // { Documentation
    /// Unlike method `swap_node`, `swap_cargo`
    /// - is an associated function, to be called as `Node::swap_cargo(...)`;
    /// - takes a `Node<C>` as a parameter, instead of a mutable reference;
    /// - allows one to swap the cargo on a root node, instead of only on subnodes.
    ///
    /// The latter is also the reason why `swap_cargo` needs the target node to be moved into its
    /// first parameter: swapping the cargo on a root node involves replacing that node with
    /// another one.
    ///
    /// This also means that, if you want to swap the cargo on a node, you'll have to retrieve it from
    /// the function's return value afterwards, or it will be dropped :
    /// ```
    /// use tree_by_path::{Node, PathError, TraverseAction};
    ///
    /// #[derive(Debug)]
    /// struct NoCopy {
    ///     value: u8,
    /// }
    /// 
    /// let mut n = Node::new(NoCopy{value: 10});
    /// let added_path = n.add_cargo_under(&vec![], NoCopy{value: 1}).unwrap();
    /// n.add_cargo_under(&vec![], NoCopy{value: 7}).unwrap();
    ///
    /// n.add_cargo_under(&added_path, NoCopy{value: 2}).unwrap();
    /// n.add_cargo_under(&added_path, NoCopy{value: 3}).unwrap();
    ///
    /// let mut total = n.traverse(
    ///     0u8,
    ///     |accum, nd, _path| {
    ///         *accum += nd.cargo.value;
    ///         TraverseAction::Continue
    ///     }
    /// );
    ///
    /// assert_eq!(23u8, total);
    ///
    /// // Moving our root node n into swap_cargo's first parameter.
    /// let swap_result = Node::swap_cargo(n, &vec![], NoCopy{value: 30u8});
    ///
    /// assert!(swap_result.is_ok());
    ///
    /// let old_cargo: NoCopy;
    ///
    /// // Getting our tree with root node n back.
    /// (n, old_cargo) = swap_result.unwrap();
    ///
    /// assert_eq!(10, old_cargo.value);
    ///
    /// total = n.traverse(
    ///     0u8,
    ///     |accum, nd, _path| {
    ///         *accum += nd.cargo.value;
    ///         TraverseAction::Continue
    ///     }
    /// );
    ///
    /// assert_eq!(43u8, total);
    ///
    /// ```
    ///
    /// If ever the swap operation would fail, the node passed as first parameter is not lost and
    /// can be retrieved from the `Err(...)` result :
    ///
    /// ```
    /// use tree_by_path::{Node, PathError};
    ///
    /// let mut n = Node::new('g');
    /// n.add_cargo_under(&vec![], 'o').unwrap();
    ///
    /// // Moving root node n into swap_cargo's first parameter ...
    /// let result = Node::swap_cargo(n, &vec![5], 'a');
    ///
    /// assert!(result.is_err());
    /// 
    /// // ... and getting it back from the function's return value.
    /// let (err, n, new_cargo) = result.unwrap_err();
    /// assert_eq!(&'g', n.borrow_cargo(&vec![]).unwrap());
    ///
    /// assert_eq!(PathError::InputPathNotFound, err);
    ///
    /// // Besides, neither the new cargo not having been swapped is lost.
    /// assert_eq!('a', new_cargo);
    /// ```
    // }
    pub fn swap_cargo(mut tree_root: Node<C>, path: &Vec<usize>, cargo: C) -> Result<(Node<C>, C), (PathError, Node<C>, C)> {

        fn transfer_children<C>(source: &mut Node<C>, target: &mut Node<C>) -> Result<(), PathError> {
            let mut child: Node<C>;

            while source.children.len() > 0 {
                child = match source.children.pop() {
                    Some(ch) => ch,
                    None => return Err(
                        PathError::ProcessError(
                            "Node.swap_cargo failed to pop() child nodes from old node.".to_string()
                        )
                    ),
                };

                target.children.insert(0, child);
            }

            Ok(())
        }

        let mut new_node = Node::new(cargo);
        let is_swap_from_root = path.len() == 0;

        if is_swap_from_root {
            match transfer_children(&mut tree_root, &mut new_node) {
                Ok(_) => (),
                Err(err) => return Err((err, tree_root, new_node.cargo)),
            }

            Ok((new_node, tree_root.cargo))
        } else {
            let old_node = match tree_root.borrow_mut_node(path) {
                Ok(node) => node,
                Err(err) => return Err((err, tree_root, new_node.cargo)),
            };
            
            match transfer_children(old_node, &mut new_node) {
                Ok(_) => (),
                Err(err) => return Err((err, tree_root, new_node.cargo)),
            }

            match tree_root.swap_node(path, new_node) {
                Ok(extracted_node) => Ok((tree_root, extracted_node.cargo)),
                Err((err, new_nd)) => Err((err, tree_root, new_nd.cargo)),
            }
        }
    }

    // { Documentation
    /// Checks if a node has a subnode having the given path.
    ///
    /// You'll rarely want to call this method: all other methods accepting an input path return a
    /// `Result::Err(...)` which will return cargo and nodes not inserted or swapped if the given
    /// path is nonexistent or not fit for the operation.
    ///
    /// In most cases, if you use this method to prevent a subsequent method call to fail, you'll
    /// just be doubling the processing involved in retrieving the node the path points at.
    // }
    pub fn has_path(&self, path: &Vec<usize>) -> bool {
        self.borrow_node(path).is_ok()
    }

    //{ Documentation
    /// Returns a `NodeIterator<'it, C> : std::iter::Iterator` which allows iteration over immutable references to a tree's
    /// cargoes.
    ///
    /// Note that use of the methods traverse and traverse_back is usually faster and more
    /// flexible.
    //}
    pub fn iter(&self) -> NodeIterator<C> {
        NodeIterator::new(self)
    }

    //{ Documentation
    /// `traverse` receives two arguments :
    /// - an initial value for an accumulator;
    /// - a callback function or closure.
    /// 'traverse' passes a node and all of its child nodes to this callback closure or function.
    /// 
    /// The callback closure receives three parameters :
    /// - a mutable reference to the accumulated value;
    /// - a mutable reference to the node passed to it;
    /// - a reference to the passed node's address or path.
    ///
    /// Unlike `std::iter::Iterator.fold`, the callback closure doesn't return the accumulated value,
    /// but a TraverseAction variant.
    ///
    /// (As the accumulated value is mutable, it can be manipulated by the callback closure.)
    ///
    /// Example : totalizing the numerical cargo of all nodes until the total reaches a certain
    /// value:
    ///
    /// ```
    /// use tree_by_path::{Node, TraverseAction};
    ///
    /// let mut n = Node::new(0);
    /// n.add_cargo_under(&vec![], 1).unwrap();
    /// n.add_cargo_under(&vec![], 2).unwrap();
    /// n.add_cargo_under(&vec![1], 3).unwrap();
    /// n.add_cargo_under(&vec![1], 4).unwrap();
    /// n.add_cargo_under(&vec![], 5).unwrap();
    ///
    /// let outcome = n.traverse(
    ///     0,
    ///     |acc, nd, _path| {
    ///         *acc += nd.cargo;
    ///
    ///         if *acc <= 5 { TraverseAction::Continue } else { TraverseAction::Stop }
    ///     }
    /// );
    ///
    /// assert_eq!(6, outcome);
    /// ```
    //}
    pub fn traverse<Accum, CallBack>(&mut self, mut init: Accum, mut call_back: CallBack) -> Accum
    where CallBack: FnMut(&mut Accum, &mut Node<C>, &Vec<usize>) -> TraverseAction {
        let mut current_path = self.get_first_path();
        let mut current_node: &mut Node<C>;

        loop {
            current_node = self.borrow_mut_node(&current_path)
                .expect("While traversing, borrowing a node should never yield Result::Err.");

            match (call_back)(&mut init, current_node, &current_path) {
                TraverseAction::Continue => (),
                TraverseAction::Stop => break,
                TraverseAction::SkipChildren => {
                    let mut last_child_index: usize;

                    // Go to last child of last child of ... of current node
                    // thus effectively causing all children of current node
                    // to be skipped.
                    while current_node.children.len() > 0 {
                        last_child_index = current_node.children.len() - 1;
                        current_path.push(last_child_index);
                        current_node = &mut current_node.children[last_child_index];
                    }
                },
            }

            current_path = match self.get_next_path(&current_path) {
                Ok(p) => p,
                _ => break,
            }
        }

        init
    }

    //{ Documentation
    /// `traverse_back` acts in a similar way as the `traverse` method, except
    /// - the nodes are visited in exactly the inverse order that `traverse` would visit them -
    ///     this means that a node's children are visited before their parent node,
    ///     and the root node is visited last.
    /// - `TraverseAction::SkipChildren` causes a node's parent to be visited next, and preceding
    ///     siblins to be skipped.
    //}
    pub fn traverse_back<Accum, CallBack>(&mut self, mut init: Accum, mut call_back: CallBack) -> Accum
    where CallBack: FnMut(&mut Accum, &mut Node<C>, &Vec<usize>) -> TraverseAction {
        let mut current_path = self.get_last_path();
        let mut current_node: &mut Node<C>;

        loop {
            current_node = self.borrow_mut_node(&current_path)
                .expect("While traversing, borrowing a node should never yield Result::Err.");

            /*
            if !(call_back)(&mut init, current_node, &current_path) {
                break;
            }
            */
            match (call_back)(&mut init, current_node, &current_path) {
                TraverseAction::Continue => (),
                TraverseAction::Stop => break,

                // One can't skip all of the current node's children
                // when traversing backward,
                // because these children are traversed first.
                // But one can ask to ignore other siblings and jump to the parent.
                TraverseAction::SkipChildren =>  {
                    let path_len = current_path.len();

                    if path_len > 0 {
                        let current_index = current_path[path_len - 1];

                        if current_index > 0 {
                            current_path[path_len - 1] = 0;
                        }
                    }
                },
            }

            current_path = match self.get_previous_path(&current_path) {
                Ok(p) => p,
                _ => break,
            }
        }

        init
    }

    pub fn borrow_node(&self, path: &Vec<usize>) -> Result<&Node<C>, PathError> {
        let mut pathix = 0usize;
        let mut current_ix: usize;
        let path_len = path.len();
        let mut nd: &Node<C> = self;

        while pathix < path_len {
            current_ix = path[pathix];

            if current_ix < nd.children.len() {
                nd = &nd.children[current_ix];
            } else {
                return Err(PathError::InputPathNotFound);
            }

            pathix += 1;
        }

        Ok(nd)
    }

    pub fn borrow_mut_node(&mut self, path: &Vec<usize>) -> Result<&mut Node<C>, PathError> {
        let mut pathix = 0usize;
        let mut current_ix: usize;
        let path_len = path.len();
        let mut nd: &mut Node<C> = self;

        while pathix < path_len {
            current_ix = path[pathix];

            if current_ix < nd.children.len() {
                nd = &mut nd.children[current_ix];
            } else {
                return Err(PathError::InputPathNotFound);
            }

            pathix += 1;
        }

        Ok(nd)
    }
}

impl <C> Node<CargoWithId<C>> {
    pub fn new_with_id(cargo: C) -> Self {
        Node::new(CargoWithId::new(cargo))
    }

    pub fn get_id(&self) -> usize {
        self.cargo.id
    }

    pub fn add_cargo_under_with_id(&mut self, path: &Vec<usize>, cargo: C) -> Result<(Vec<usize>, usize), (PathError, C)> {
        let cargo_with_id = CargoWithId::new(cargo);
        let id = cargo_with_id.id;

        match self.add_cargo_under(path, cargo_with_id) {
            Ok(new_path) => Ok((new_path, id)),
            Err((err, crg)) => Err((err, crg.subcargo)),
        }
    }

    pub fn add_cargo_after_with_id(&mut self, path: &Vec<usize>, cargo: C) -> Result<(Vec<usize>, usize), (PathError, C)> {
        let cargo_with_id = CargoWithId::new(cargo);
        let id = cargo_with_id.id;

        match self.add_cargo_after(path, cargo_with_id) {
            Ok(new_path) => Ok((new_path, id)),
            Err((err, crg)) => Err((err, crg.subcargo)),
        }
    }

    pub fn add_cargo_before_with_id(&mut self, path: &Vec<usize>, cargo: C) -> Result<(Vec<usize>, usize), (PathError, C)> {
        let cargo_with_id = CargoWithId::new(cargo);
        let id = cargo_with_id.id;

        match self.add_cargo_before(path, cargo_with_id) {
            Ok(new_path) => Ok((new_path, id)),
            Err((err, crg)) => Err((err, crg.subcargo)),
        }
    }

    pub fn borrow_cargo_get_path_by_id(&self, id: &usize) -> Result<(&C, Vec<usize>), PathError> {
        let mut current_path = self.get_first_path();
        let mut current_node: &Node<CargoWithId<C>>;
        let mut result = Err(PathError::InputIdNotFound);

        loop {
            current_node = self.borrow_node(&current_path)
                .expect("While traversing, borrowing a node should never yield Result::Err.");

            if &current_node.cargo.id == id {
                result = Ok((&current_node.cargo.subcargo, current_path));
                break;
            }

            current_path = match self.get_next_path(&current_path) {
                Ok(p) => p,
                _ => break,
            }
        }

        result
    }

    pub fn borrow_cargo_by_id(&self, id: &usize) -> Result<&C, PathError> {
        match self.borrow_cargo_get_path_by_id(id) {
            Ok((crg, _)) => Ok(crg),
            Err(err) => Err(err),
        }
    }
}

impl<C> Clone for Node<C>
where C: Clone {
    fn clone(&self) -> Self {
        Node {
            cargo: self.cargo.clone(),
            children: self.children.clone(),
        }
    }
}

//{ Documentation
/// A `TraverseAction` variant is expected as the return value of the callback closure or function
/// passed to `Node`'s `traverse` or `traverse_back` methods.
//}
pub enum TraverseAction {
    /// Tells the traverse* methods to continue traversing the tree.
    Continue,

    /// Tells the traverse method to skip all children of the node being handled by the callback
    /// closure.
    /// The traverse_back method, who visits a node's children first, will jump immediately to the
    /// parent of the node being handled, thus skipping all preceding siblings.
    SkipChildren,

    /// Tells the traverse* methods to stop the tree traversal, so no more nodes will be visited.
    Stop,
}

pub struct CargoWithId<Crg> {
    id: usize,
    subcargo: Crg,
}

impl <Crg> CargoWithId<Crg> {
    pub fn new(subcargo: Crg) -> Self {
        CargoWithId {
            id: Self::get_next_id(),
            subcargo: subcargo,
        }
    }

    pub fn get_next_id() -> usize {
        static ID_COUNTER: AtomicUsize = AtomicUsize::new(0);

        let return_value = ID_COUNTER.load(Ordering::SeqCst);
        ID_COUNTER.store(return_value + 1, Ordering::SeqCst);

        return_value
    }
}

impl<Crg> Clone for CargoWithId<Crg>
where Crg: Clone {
    fn clone(&self) -> Self {
        CargoWithId::new(self.subcargo.clone())
    }
}

#[derive(PartialEq, Debug)]
pub enum PathError {
    /// Means that the path passed to a Node method doesn't exist.
    InputPathNotFound,

    /// Means that, even if the path passed to a Node method does exist, the operation still can't
    /// be performed. E.g.: no node can be added to a tree after the root node (only under it).
    InputPathNotFitForOperation,

    /// Means that the output path that would be returned by a Node method doesn't exist. E.g.:
    /// calling `Node.get_next_path(&the_path_of_the_last_node)`
    RequestedPathNotAvailable,

    /// Means that the id passed to a method of a Node<CargoWithId<C>> wasn't found in the tree.
    InputIdNotFound,

    /// Means that an unforeseen error occurred. In theory, this should never happen.
    /// (In theory, the difference between theory and practice is extremely small.<br />
    /// In practice, however ...)
    ProcessError(String),
}

    //{ Documentation
    /// `NodeIterator<'it, C> : std::iter::Iterator` allows iteration over immutable references to a tree's
    /// cargoes.
    ///
    /// Note that use of the traverse and traverse_back methods is faster and allows for more flexibility, like
    /// - skipping a node's children,
    /// - prematurely stopping the iteration,
    /// - inspecting the nodes' path,
    /// - changing a node's cargo,
    /// - changing a node's children collection.
    ///
    /// The order the nodes are iterated over by the `next` and `next_back` methods is the same as the
    /// order used by the `Node.traverse` and `Node.traverse_back` methods.
    //}
pub struct NodeIterator<'it, C> {
    root: &'it Node<C>,
    current_path: Vec<usize>,
    is_fresh: bool,
    back_current_path: Vec<usize>,
    back_is_fresh: bool,
}

impl<'it, C> NodeIterator<'it, C> {
    pub fn new(root: &'it Node<C>) -> NodeIterator<'it, C> {
        NodeIterator {
            root: root,
            current_path: Vec::<usize>::new(),
            is_fresh: true,
            back_current_path: root.get_last_path(),
            back_is_fresh: true,
        }
    }

    fn get_freshness(&mut self, is_forward: bool) -> bool {
        if is_forward {self.is_fresh} else {self.back_is_fresh}
    }

    fn set_unfresh(&mut self, is_forward: bool) {
        if is_forward {
            self.is_fresh = false;
        } else {
            self.back_is_fresh = false;
        }
    }

    fn set_next_path(&mut self, is_forward:bool) -> bool {
        let mut has_next = true;

        if self.get_freshness(is_forward) {
            self.set_unfresh(is_forward);
        } else { 
            let next_path_result: Result<Vec<usize>, PathError>;

            if is_forward {
                next_path_result = self.root.get_next_path(&self.current_path);
            } else {
                next_path_result = self.root.get_previous_path(&self.back_current_path);
            }

            match next_path_result {
                Ok(next_path) => {
                    let no_next_back_crossing = if is_forward {
                        next_path < self.back_current_path
                    } else {
                        next_path > self.current_path
                    };

                    if (self.get_freshness(!is_forward)) || no_next_back_crossing {
                        if is_forward {
                            self.current_path = next_path;
                        } else {
                            self.back_current_path = next_path;
                        }
                    } else {
                        has_next = false;
                    }
                },
                _ => has_next = false,
            }
        }

        has_next
    }
}

impl<'it, C> Iterator for NodeIterator<'it, C> {
    type Item = &'it C;

    fn next(&mut self) -> Option<Self::Item> {
        let has_next = self.set_next_path(true);

        match has_next {
            true => Some(self.root.borrow_cargo(&self.current_path).unwrap()),
            false => None,
        }
    }
}

impl<'it, C> DoubleEndedIterator for NodeIterator<'it, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let has_next = self.set_next_path(false);

        match has_next {
            true => Some(self.root.borrow_cargo(&self.back_current_path).unwrap()),
            false => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_new() {
        let n = Node::new(4u8);

        assert_eq!(4u8, n.cargo);
        assert_eq!(0, n.children.len());
    }

    #[test]
    fn node_borrow_node() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&Node<u8>, PathError>;

        borrowed = n.borrow_node(&Vec::<usize>::new());
        assert!(borrowed.is_ok());
        assert_eq!(0, borrowed.unwrap().cargo);

        borrowed = n.borrow_node(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(2, borrowed.unwrap().cargo);

        borrowed = n.borrow_node(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(5, borrowed.unwrap().cargo);

        borrowed = n.borrow_node(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_node(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(3, borrowed.unwrap().cargo);

        borrowed = n.borrow_node(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(4, borrowed.unwrap().cargo);

        borrowed = n.borrow_node(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_node(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_borrow_mut_node() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&mut Node<u8>, PathError>;

        borrowed = n.borrow_mut_node(&Vec::<usize>::new());
        assert!(borrowed.is_ok());
        assert_eq!(0, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(2, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(5, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_node(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(3, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(4, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_node(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_borrow_cargo() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&u8, PathError>;

        borrowed = n.borrow_cargo(&Vec::<usize>::new());
        assert!(borrowed.is_ok());
        assert_eq!(&0, borrowed.unwrap());

        borrowed = n.borrow_cargo(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(&2, borrowed.unwrap());

        borrowed = n.borrow_cargo(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(&5, borrowed.unwrap());

        borrowed = n.borrow_cargo(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_cargo(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(&3, borrowed.unwrap());

        borrowed = n.borrow_cargo(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(&4, borrowed.unwrap());

        borrowed = n.borrow_cargo(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_cargo(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_borrow_mut_cargo() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&mut u8, PathError>;

        // Check if we can read twice.
        for _i in 0..2 {
            borrowed = n.borrow_mut_cargo(&Vec::<usize>::new());
            assert!(borrowed.is_ok());
            assert_eq!(&mut 0, borrowed.unwrap());
        }

        borrowed = n.borrow_mut_cargo(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 2, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 5, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_cargo(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 3, borrowed.unwrap());

        // Check if we can change the cargo.
        borrowed = n.borrow_mut_cargo(&vec![1, 1]);
        assert!(borrowed.is_ok());
        let unwrapped = borrowed.unwrap();
        assert_eq!(&mut 4, unwrapped);
        *unwrapped = 40;
        borrowed = n.borrow_mut_cargo(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 40, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_cargo(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_add_cargo_under() {
        let mut n = Node::new(0u8);
        let mut result: Result<Vec<usize>, (PathError, u8)>;

        result = n.add_cargo_under(&vec![], 1);
        assert!(result.is_ok());
        assert_eq!(vec![0], result.unwrap());

        result = n.add_cargo_under(&vec![], 2);
        assert!(result.is_ok());
        assert_eq!(vec![1], result.unwrap());
        assert_eq!(&2, n.borrow_cargo(&vec![1]).unwrap());

        result = n.add_cargo_under(&vec![0], 3);
        assert!(result.is_ok());
        assert_eq!(vec![0, 0], result.unwrap());

        result = n.add_cargo_under(&vec![0], 4);
        assert!(result.is_ok());
        assert_eq!(vec![0, 1], result.unwrap());

        let borrowed = n.borrow_cargo(&vec![0, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(&4, borrowed.unwrap());

        result = n.add_cargo_under(&vec![50], 99);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound,99), result.unwrap_err());

        result = n.add_cargo_under(&vec![0, 1, 1], 99);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound,99), result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_after_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, (PathError, i8)>;

        result = n.add_cargo_after(&vec![], -38);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation, -38), result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_after() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, (PathError, i8)>;
        let mut result_path: Vec<usize>;

        result = n.add_cargo_after(&vec![0], 1);
        assert!(result.is_err());
        assert_eq!((PathError::RequestedPathNotAvailable, 1), result.unwrap_err());

        n.add_cargo_under(&vec![], 1).unwrap();

        result = n.add_cargo_after(&vec![0], 2);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&2, n.borrow_cargo(&result_path).unwrap());

        result = n.add_cargo_after(&vec![0], 3);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo(&result_path).unwrap());
        assert_eq!(&2, n.borrow_cargo(&vec![2]).unwrap());
    }

    #[test]
    fn node_add_cargo_before_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, (PathError, i8)>;

        result = n.add_cargo_before(&vec![], -38);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation,-38), result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_before() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, (PathError, i8)>;
        let mut result_path: Vec<usize>;

        result = n.add_cargo_before(&vec![0], 1);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&1, n.borrow_cargo(&result_path).unwrap());

        result = n.add_cargo_before(&vec![0], 2);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&2, n.borrow_cargo(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo(&vec![1]).unwrap());

        result = n.add_cargo_before(&vec![1], 3);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo(&vec![2]).unwrap());

        result = n.add_cargo_before(&vec![0, 0], 4);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0, 0], result_path);
        assert_eq!(&4, n.borrow_cargo(&result_path).unwrap());

        result = n.add_cargo_before(&vec![2, 1], 5);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound,5), result.unwrap_err());
    }

    #[test]
    fn node_get_next_on_lone_root() {
        let n = Node::new(0u8);
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_next_path(&vec![]));
    }

    #[test]
    fn node_get_next_input_not_found() {
        let n = Node::new(0u8);
        assert_eq!(Err(PathError::InputPathNotFound), n.get_next_path(&vec![5]));
    }

    #[test]
    fn node_get_next_from_last() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_next_path(&vec![1]));
    }

    #[test]
    #[should_panic]
    fn node_get_next_from_last_unwrap() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        let path_result = n.get_next_path(&vec![1]);
        path_result.unwrap();
    }

    #[test]
    fn node_get_next_next_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();

        let path_result = n.get_next_path(&vec![0]);
        assert!(path_result.is_ok());
        let next_path = path_result.unwrap();
        assert_eq!(vec![1], next_path);
        assert_eq!(&2, n.borrow_cargo(&next_path).unwrap());
    }

    #[test]
    fn node_get_next_root_to_child() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        assert_eq!(Ok(vec![0]), n.get_next_path(&vec![]));
    }

    #[test]
    fn node_get_next_non_root_to_child() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_after(&vec![1], 4).unwrap();
        assert_eq!(Ok(vec![1, 0]), n.get_next_path(&vec![1]));
    }

    #[test]
    fn node_get_next_non_child_to_parents_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_after(&vec![1], 4).unwrap();
        assert_eq!(Ok(vec![2]), n.get_next_path(&vec![1, 0]));
    }

    #[test]
    fn node_get_next_non_child_to_grandparents_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1, 0], 4).unwrap();
        n.add_cargo_after(&vec![1], 5).unwrap();
        assert_eq!(Ok(vec![2]), n.get_next_path(&vec![1, 0, 0]));
    }

    #[test]
    fn node_get_next_from_last_is_grandchild() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1, 0], 4).unwrap();
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_next_path(&vec![1, 0, 0]));
    }

    #[test]
    fn node_get_previous_from_unexistent() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1, 0], 4).unwrap();
        assert_eq!(Err(PathError::InputPathNotFound), n.get_next_path(&vec![3, 0, 0]));
    }

    #[test]
    fn node_get_previous_from_root() {
        let n = Node::new(String::from("aaa"));
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_previous_path(&vec![]));
    }

    #[test]
    fn node_get_previous() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_after(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1, 0], 4).unwrap();
        n.add_cargo_after(&vec![1], 5).unwrap();
        n.add_cargo_after(&vec![2], 6).unwrap();
        n.add_cargo_after(&vec![1, 0], 50).unwrap();
        n.add_cargo_under(&vec![1, 1], 51).unwrap();
        n.add_cargo_after(&vec![1, 1, 0], 52).unwrap();

        /*
         *  0
         *  |
         *  1--2----------5--6
         *     |
         *     3--50
         *     |  |
         *     4  51--52
        */

        let mut path_result: Result<Vec<usize>, PathError>;
        let mut previous: Vec<usize>;

        // Descend to last grandchild under previous sibling.
        path_result = n.get_previous_path(&vec![2]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 1, 1], previous);
        assert_eq!(&52, n.borrow_cargo(&previous).unwrap());

        // Descend to last grandchild under previous sibling (bis)
        path_result = n.get_previous_path(&vec![1, 1]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 0, 0], previous);
        assert_eq!(&4, n.borrow_cargo(&previous).unwrap());

        // Find previous sibling
        path_result = n.get_previous_path(&vec![1, 1, 1]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 1, 0], previous);
        assert_eq!(&51, n.borrow_cargo(&previous).unwrap());

        // Find previous sibling (bis)
        path_result = n.get_previous_path(&vec![1]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![0], previous);
        assert_eq!(&1, n.borrow_cargo(&previous).unwrap());

        // Find non-root parent
        path_result = n.get_previous_path(&vec![1, 1, 0]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 1], previous);
        assert_eq!(&50, n.borrow_cargo(&previous).unwrap());
        
        // Find root parent
        path_result = n.get_previous_path(&vec![0]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(Vec::<usize>::new(), previous);
        assert_eq!(&0, n.borrow_cargo(&previous).unwrap());
    }

    #[test]
    fn node_get_last_on_lone_root() {
        let n = Node::new('K');
        let result = n.get_last_path();
        assert_eq!(Vec::<usize>::new(), result);
    }

    #[test]
    fn node_get_last_on_lone_child() {
        let mut n = Node::new('K');
        n.add_cargo_under(&vec![], 'Z').unwrap();
        let result = n.get_last_path();
        assert_eq!(vec![0usize], result);
    }

    #[test]
    fn node_get_last_on_first_level() {
        let mut n = Node::new('A');
        n.add_cargo_under(&vec![], 'B').unwrap();
        n.add_cargo_under(&vec![], 'C').unwrap();
        n.add_cargo_under(&vec![], 'D').unwrap();
        let result = n.get_last_path();
        assert_eq!(vec![2usize], result);
        assert_eq!(&'D', n.borrow_cargo(&vec![2]).unwrap());
    }

    #[test]
    fn node_extract_node_by_root() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&n.get_first_path(), 1).unwrap();
        let result = n.extract_node(&n.get_first_path());
        assert!(result.is_err());
        assert_eq!(PathError::InputPathNotFitForOperation, result.unwrap_err());
    }

    #[test]
    fn node_extract_node_by_nonexistent() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&n.get_first_path(), 1).unwrap();
        let result = n.extract_node(&vec![0, 3]);
        assert!(result.is_err());
        assert_eq!(PathError::InputPathNotFound, result.unwrap_err());
    }

    #[test]
    fn node_extract_node_by_lone_leaf() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&n.get_first_path(), 1).unwrap();
        let result = n.extract_node(&vec![0]);
        assert!(result.is_ok());
        let nd = result.unwrap();
        assert_eq!(1, nd.cargo);
    }

    #[test]
    fn node_extract_node_by_lone_non_leaf() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&n.get_first_path(), 1).unwrap();
        n.add_cargo_under(&vec![0], 2).unwrap();
        n.add_cargo_under(&vec![0], 3).unwrap();
        let result = n.extract_node(&vec![0]);
        assert!(result.is_ok());
        let nd = result.unwrap();
        assert_eq!(1, nd.cargo);
        assert!(nd.borrow_cargo(&vec![1]).is_ok());
    }

    #[test]
    fn node_extract_node_by_non_leaf() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 90).unwrap();
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_under(&vec![], 91).unwrap();
        n.add_cargo_under(&vec![1], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        let result = n.extract_node(&vec![1]);
        assert!(result.is_ok());
        let nd = result.unwrap();
        assert_eq!(1, nd.cargo);
        assert!(nd.borrow_cargo(&vec![1]).is_ok());
        assert!(!n.has_path(&vec![2]));
        assert_eq!(&91, n.borrow_cargo(&vec![1]).unwrap());
    }

    #[test]
    fn node_add_node_under_nonexistent() {
        let mut n = Node::new(0u8);
        let n1 = Node::new(1u8);
        let result: Result<Vec<usize>, (PathError, Node<u8>)>;

        result = n.add_node_under(&vec![2, 4], n1);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::InputPathNotFound, err);
        assert_eq!(&1u8, bounced_node.borrow_cargo(&vec![]).unwrap());
    }

    #[test]
    fn node_add_node_under() {
        let mut n = Node::new(0u8);
        let n1 = Node::new(1u8);
        let result: Result<Vec<usize>, (PathError, Node<u8>)>;
        let result_path: Vec<usize>;

        result = n.add_node_under(&vec![], n1);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&1, n.borrow_cargo(&result_path).unwrap());
    }

    #[test]
    fn node_add_node_after_empty() {
        let mut n = Node::new(0i8);
        let n1 = Node::new(-38i8);
        let result: Result<Vec<usize>, (PathError, Node<i8>)>;

        result = n.add_node_after(&vec![], n1);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation, Node::new(-38i8)), result.unwrap_err());
    }

    #[test]
    fn node_add_node_after() {
        let mut n = Node::new(0i8);
        let n1 = Node::new(1i8);
        let mut result: Result<Vec<usize>, (PathError, Node<i8>)>;
        let mut result_path: Vec<usize>;

        result = n.add_node_after(&vec![0], n1);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::RequestedPathNotAvailable, err);
        assert_eq!(Node::new(1i8), bounced_node);

        n.add_node_under(&vec![], bounced_node).unwrap();

        result = n.add_node_after(&vec![0], Node::new(2i8));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&2, n.borrow_cargo(&result_path).unwrap());

        result = n.add_node_after(&vec![0], Node::new(3));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo(&result_path).unwrap());
        assert_eq!(&2, n.borrow_cargo(&vec![2]).unwrap());
    }

    #[test]
    fn node_add_node_before_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, (PathError, Node<i8>)>;

        result = n.add_node_before(&vec![], Node::new(-38));
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation, Node::new(-38)), result.unwrap_err());
    }

    #[test]
    fn node_add_node_before() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, (PathError, Node<i8>)>;
        let mut result_path: Vec<usize>;

        result = n.add_node_before(&vec![0], Node::new(1));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&1, n.borrow_cargo(&result_path).unwrap());

        result = n.add_node_before(&vec![0], Node::new(2));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&2, n.borrow_cargo(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo(&vec![1]).unwrap());

        result = n.add_node_before(&vec![1], Node::new(3));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo(&vec![2]).unwrap());

        result = n.add_node_before(&vec![0, 0], Node::new(4));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0, 0], result_path);
        assert_eq!(&4, n.borrow_cargo(&result_path).unwrap());

        result = n.add_node_before(&vec![2, 1], Node::new(5));
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound, Node::new(5)), result.unwrap_err());
    }
    
    #[test]
    fn node_swap_node_by_root() {
        let mut n = Node::new(0u8);
        let to_swap = Node::new(1u8);
        let result = n.swap_node(&vec![], to_swap);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::InputPathNotFitForOperation, err);
        assert_eq!(&1u8, bounced_node.borrow_cargo(&vec![]).unwrap());
    }

    #[test]
    fn node_swap_node_by_nonexistent() {
        let mut n = Node::new(0u8);
        let to_swap = Node::new(1u8);
        let result = n.swap_node(&vec![8], to_swap);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::InputPathNotFound, err);
        assert_eq!(&1u8, bounced_node.borrow_cargo(&vec![]).unwrap());
    }
    
    #[test]
    fn node_swap_node() {
        let mut n = Node::new(0u8);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_under(&vec![], 2).unwrap();
        n.add_cargo_under(&vec![], 3).unwrap();
        n.add_cargo_under(&vec![1], 20).unwrap();
        n.add_cargo_under(&vec![1], 21).unwrap();
        n.add_cargo_under(&vec![1], 22).unwrap();

        let mut to_swap = Node::new(9u8);
        to_swap.add_cargo_under(&vec![], 90).unwrap();
        to_swap.add_cargo_under(&vec![], 91).unwrap();
        to_swap.add_cargo_under(&vec![], 92).unwrap();
        to_swap.add_cargo_under(&vec![], 93).unwrap();

        let result = n.swap_node(&vec![1], to_swap);
        assert!(result.is_ok());
        let removed = result.unwrap();

        assert_eq!(4, n.borrow_node(&vec![1]).unwrap().children.len());
        assert_eq!(3, removed.children.len());

        assert_eq!(&9, n.borrow_cargo(&vec![1]).unwrap());
        assert_eq!(&93, n.borrow_cargo(&vec![1, 3]).unwrap());
        assert_eq!(&2, removed.borrow_cargo(&vec![]).unwrap());
        assert_eq!(&22, removed.borrow_cargo(&vec![2]).unwrap());
    }

    #[test]
    fn node_iter_lone_root() {
        let n = Node::new('A');

        let concat = n.iter().fold(
            String::new(),
            |mut accu: String, cargo: &char| {
                accu.push(*cargo);
                accu
            }
        );

        assert_eq!("A".to_string(), concat);
    }

    #[test]
    fn node_iter_back_lone_root() {
        let n = Node::new('A');

        let concat = n.iter().rfold(
            String::new(),
            |mut accu: String, cargo: &char| {
                accu.push(*cargo);
                accu
            }
        );

        assert_eq!("A".to_string(), concat);
    }

    #[test]
    fn node_iter() {
        let mut n = Node::new('A');
        n.add_cargo_under(&vec![], 'B').unwrap();
        n.add_cargo_under(&vec![], 'C').unwrap();
        n.add_cargo_under(&vec![], 'D').unwrap();
        n.add_cargo_under(&vec![2], 'E').unwrap();
        n.add_cargo_under(&vec![2], 'F').unwrap();
        n.add_cargo_under(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under(&vec![], 'H').unwrap();

        let concat = n.iter().fold(
            String::new(),
            |mut accu: String, cargo: &char| {
                accu.push(*cargo);
                accu
            }
        );

        assert_eq!("ABCDEFGH".to_string(), concat);
    }

    #[test]
    fn node_iter_back() {
        let mut n = Node::new('A');
        n.add_cargo_under(&vec![], 'B').unwrap();
        n.add_cargo_under(&vec![], 'C').unwrap();
        n.add_cargo_under(&vec![], 'D').unwrap();
        n.add_cargo_under(&vec![2], 'E').unwrap();
        n.add_cargo_under(&vec![2], 'F').unwrap();
        n.add_cargo_under(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under(&vec![], 'H').unwrap();

        let concat = n.iter().rfold(
            String::new(),
            |mut accu: String, cargo: &char| {
                accu.push(*cargo);
                accu
            }
        );

        assert_eq!("HGFEDCBA".to_string(), concat);
    }

    #[test]
    fn node_iter_next_back_dont_cross() {
        let mut n = Node::new('A');
        n.add_cargo_under(&vec![], 'B').unwrap();
        n.add_cargo_under(&vec![], 'C').unwrap();
        n.add_cargo_under(&vec![], 'D').unwrap();
        n.add_cargo_under(&vec![2], 'E').unwrap();
        n.add_cargo_under(&vec![2], 'F').unwrap();
        n.add_cargo_under(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under(&vec![], 'H').unwrap();

        let mut concat = String::new();
        let mut iter = n.iter();
        let mut no_next = false;
        let mut no_back = false;

        loop {
            if !no_next {
                match iter.next() {
                    Some(ch) => concat.push(*ch),
                    None => no_next = true,
                }
            }

            if !no_back {
                match iter.next_back() {
                    Some(ch) => concat.push(*ch),
                    None => no_back = true,
                }
            }

            if no_next && no_back {
                break;
            }
        }

        assert_eq!("AHBGCFDE", concat);
    }

    #[test]
    fn node_iter_back_next_dont_cross() {
        let mut n = Node::new('A');
        n.add_cargo_under(&vec![], 'B').unwrap();
        n.add_cargo_under(&vec![], 'C').unwrap();
        n.add_cargo_under(&vec![], 'D').unwrap();
        n.add_cargo_under(&vec![2], 'E').unwrap();
        n.add_cargo_under(&vec![2], 'F').unwrap();
        n.add_cargo_under(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under(&vec![], 'H').unwrap();

        let mut concat = String::new();
        let mut iter = n.iter();
        let mut no_next = false;
        let mut no_back = false;

        loop {
            if !no_back {
                match iter.next_back() {
                    Some(ch) => concat.push(*ch),
                    None => no_back = true,
                }
            }

            if !no_next {
                match iter.next() {
                    Some(ch) => concat.push(*ch),
                    None => no_next = true,
                }
            }

            if no_next && no_back {
                break;
            }
        }

        assert_eq!("HAGBFCED", concat);
    }

    #[test]
    fn node_traverse_lone_root() {
        let mut n = Node::new(38);

        let outcome = n.traverse(
            0,
            |acc, nd, _path| {
                *acc += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(38, outcome);
    }

    #[test]
    fn node_traverse_and_change() {
        let mut n = Node::new(0);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_under(&vec![], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1], 4).unwrap();
        n.add_cargo_under(&vec![], 5).unwrap();

        let mut outcome = n.traverse(
            0,
            |acc, nd, path| {
                if path.len() == 1 {
                    nd.cargo *= 2;
                    *acc += 1;
                }

                TraverseAction::Continue
            }
        );

        assert_eq!(3, outcome);

        outcome = n.traverse(
            0,
            |acc, nd, _path| {
                *acc += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(23, outcome);
    }

    #[test]
    fn node_traverse_back_and_change() {
        let mut n = Node::new(0);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_under(&vec![], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1], 4).unwrap();
        n.add_cargo_under(&vec![], 5).unwrap();

        let mut outcome = n.traverse_back(
            0,
            |acc, nd, path| {
                if path.len() == 1 {
                    nd.cargo *= 2;
                    *acc += 1;
                }

                TraverseAction::Continue
            }
        );

        assert_eq!(3, outcome);

        outcome = n.traverse_back(
            0,
            |acc, nd, _path| {
                *acc += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(23, outcome);
    }

    #[test]
    fn node_traverse_break() {
        let mut n = Node::new(0);
        n.add_cargo_under(&vec![], 1).unwrap();
        n.add_cargo_under(&vec![], 2).unwrap();
        n.add_cargo_under(&vec![1], 3).unwrap();
        n.add_cargo_under(&vec![1], 4).unwrap();
        n.add_cargo_under(&vec![], 5).unwrap();

        let outcome = n.traverse(
            0,
            |acc, nd, _path| {
                *acc += nd.cargo;

                if *acc <= 5 { TraverseAction::Continue } else { TraverseAction::Stop }
            }
        );

        assert_eq!(6, outcome);
    }

    #[test]
    fn node_traverse_skip_children_on_lone_root() {
        let mut n = Node::new('A');

        let count_nodes = n.traverse(
            0usize,
            |accum, _nd, _path| {
                *accum += 1;

                TraverseAction::SkipChildren
            }
        );

        assert_eq!(1usize, count_nodes);
    }

    #[test]
    fn node_traverse_skip_children() {
        let mut n = Node::new(0);   
        let root_path = n.get_first_path();
        let deeper_path: Vec<usize>;

        let mut root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 1).unwrap();
        n.add_cargo_under(&root_child_path, 2).unwrap();
        n.add_cargo_under(&root_child_path, 3).unwrap();

        root_child_path = n.add_cargo_under(&root_path, 100).unwrap();
        n.add_cargo_under(&root_child_path, 4).unwrap();
        n.add_cargo_under(&root_child_path, 5).unwrap();
        deeper_path = n.add_cargo_under(&root_child_path, 6).unwrap();
        n.add_cargo_under(&deeper_path, 50).unwrap();

        root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 7).unwrap();
        n.add_cargo_under(&root_child_path, 8).unwrap();
        n.add_cargo_under(&root_child_path, 9).unwrap();

        let sum = n.traverse(
            0,
            |accum, nd, _path| {
                *accum += nd.cargo;

                match nd.cargo {
                    100 => TraverseAction::SkipChildren,
                    _ => TraverseAction::Continue,
                }
            }
        );

        assert_eq!(130, sum);
    }

    #[test]
    fn node_traverse_back_skip_children() {
        let mut n = Node::new(0);   
        let root_path = n.get_first_path();

        let mut root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 1).unwrap();
        n.add_cargo_under(&root_child_path, 2).unwrap();
        n.add_cargo_under(&root_child_path, 3).unwrap();

        root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 4).unwrap();
        n.add_cargo_under(&root_child_path, 5).unwrap();
        n.add_cargo_under(&root_child_path, 6).unwrap();

        root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 7).unwrap();
        n.add_cargo_under(&root_child_path, 8).unwrap();
        n.add_cargo_under(&root_child_path, 9).unwrap();

        let sum = n.traverse_back(
            0,
            |accum, nd, _path| {
                if nd.cargo > 6 {
                    TraverseAction::SkipChildren
                } else {
                    *accum += nd.cargo;
                    TraverseAction::Continue
                }
            }
        );

        assert_eq!(21, sum);
    }

    #[test]
    fn node_traverse_back_skip_children_on_first_child() {
        let mut n = Node::new(0);   
        let root_path = n.get_first_path();

        let mut root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 1).unwrap();
        n.add_cargo_under(&root_child_path, 2).unwrap();
        n.add_cargo_under(&root_child_path, 3).unwrap();

        root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 4).unwrap();
        n.add_cargo_under(&root_child_path, 5).unwrap();
        n.add_cargo_under(&root_child_path, 6).unwrap();

        root_child_path = n.add_cargo_under(&root_path, 0).unwrap();
        n.add_cargo_under(&root_child_path, 7).unwrap();
        n.add_cargo_under(&root_child_path, 8).unwrap();
        n.add_cargo_under(&root_child_path, 9).unwrap();

        let sum = n.traverse_back(
            0,
            |accum, nd, _path| {
                if nd.cargo == 4 {
                    TraverseAction::SkipChildren
                } else {
                    *accum += nd.cargo;
                    TraverseAction::Continue
                }
            }
        );

        assert_eq!(41, sum);
    }

    #[test]
    fn node_traverse_back_skip_children_on_lone_root() {
        let mut n = Node::new('A');

        let count_nodes = n.traverse_back(
            0usize,
            |accum, _nd, _path| {
                *accum += 1;

                TraverseAction::SkipChildren
            }
        );

        assert_eq!(1usize, count_nodes);
    }

    #[test]
    fn node_set_cargo_on_root() {
        let mut n = Node::new('a');
        n.add_cargo_under(&vec![], 'b').unwrap();
        n.add_cargo_under(&vec![], 'c').unwrap();

        let result = n.set_cargo(&vec![], 'z');
        assert!(result.is_ok());
        assert_eq!(&'z', n.borrow_cargo(&vec![]).unwrap());
    }

    #[test]
    fn node_set_cargo_wrong_path() {
        let mut n = Node::new('a');
        n.add_cargo_under(&vec![], 'b').unwrap();
        n.add_cargo_under(&vec![], 'c').unwrap();

        let result = n.set_cargo(&vec![1, 3], 'z');
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound, 'z'), result.unwrap_err());
    }

    #[test]
    fn node_set_cargo() {
        let mut n = Node::new('a');
        n.add_cargo_under(&vec![], 'b').unwrap();
        n.add_cargo_under(&vec![], 'c').unwrap();

        let result = n.set_cargo(&vec![1], 'z');
        assert!(result.is_ok());
        assert_eq!(&'z', n.borrow_cargo(&vec![1]).unwrap());
    }

    #[test]
    #[ignore]
    fn node_50_000_subnodes() {
        let mut n = Node::new(0usize);
        let total_siblings = 10usize;
        let total_nodes = total_siblings * 5000usize;
        let mut siblings_count = 1usize;
        let mut path = Vec::<usize>::new();

        for crg in 0usize..total_nodes {
            if siblings_count < total_siblings {
                n.add_cargo_under(&path, crg).unwrap();
                siblings_count += 1;
            } else {
                path = n.add_cargo_under(&path, crg).unwrap();
                siblings_count = 1;
            }
        }
        
        // traverse is faster than iter().fold.
        let outcome = n.traverse(
            0usize,
            |acc, _crg, _path| {
                *acc += 1;
                TraverseAction::Continue
            }
        );

        assert_eq!(total_nodes + 1, outcome);
        assert_eq!(total_nodes / total_siblings, path.len());

        // Outcome :
        // - test lasts ca. 35.7 seconds using n.iter().fold();
        // - test lasts ca. 33.2 seconds using n.traverse();
        // - test lasts ca.  8.3 seconds without any of these, so just for building the tree
        // holding 50,001 nodes.
    }

    #[test]
    fn node_clone_clonable_cargo() {
        let mut n = Node::new(0u8);
        let mut path: Vec<usize> = Vec::new();

        for i in 1u8..4 {
            path = n.add_cargo_under(&vec![], i).unwrap();
        }

        for i in 4u8..7 {
            n.add_cargo_under(&path, i).unwrap();
        }

        let orig_total = n.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(21u8, orig_total);

        let mut nc = n.clone();

        let mut clone_total = nc.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(orig_total, clone_total);

        // Add 1 to all cargoes of the clone.
        let clone_node_count = nc.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += 1u8;
                nd.cargo += 1u8;
                TraverseAction::Continue
            }
        );

        assert_eq!(7u8, clone_node_count);

        clone_total = nc.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(orig_total + clone_node_count, clone_total);

        // Check if values of original haven't changed.

        let new_orig_total = n.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo;
                TraverseAction::Continue
            }
        );

        assert_eq!(orig_total, new_orig_total);
    }

    /*
    #[test]
    fn node_clone_non_clonable_cargo() {
        #[derive(Debug)]
        struct NoClone {}

        let mut n = Node::new(NoClone{});
        n.add_cargo_under(&Vec::<usize>::new(), NoClone{}).unwrap();

        // The below statement doesn't even compile, quod erat demonstrandum :
        // error[E0599]: the method `clone` exists for struct `Node<NoClone>`, but its trait bounds were not satisfied
        // let nc = n.clone();
    }
    */

    #[test]
    fn node_traverse_change_children() {
        let mut n = Node::new(0u8);
        let root_path = n.get_first_path();

        for i in 1u8..4 {
            n.add_cargo_under(&root_path, i).unwrap();
        }

        n.traverse(
            0u8,
            |_accum, nd, _path| {
                if nd.cargo == 2 {
                    nd.add_cargo_under(&root_path, 4u8).unwrap();
                }
                TraverseAction::Continue
            }
        );

        assert_eq!(&4u8, n.borrow_cargo(&vec![1usize, 0usize]).unwrap());
    }

    #[test]
    fn node_swap_cargo_non_root() {

        #[derive(Debug)]
        struct NoCopy {
            value: u8,
        }

        let mut n = Node::new(NoCopy{value: 10});
        let added_path = n.add_cargo_under(&vec![], NoCopy{value: 1}).unwrap();
        n.add_cargo_under(&vec![], NoCopy{value: 7}).unwrap();

        n.add_cargo_under(&added_path, NoCopy{value: 2}).unwrap();
        n.add_cargo_under(&added_path, NoCopy{value: 3}).unwrap();

        let mut total = n.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo.value;
                TraverseAction::Continue
            }
        );

        assert_eq!(23u8, total);

        let swap_result = Node::swap_cargo(n, &added_path, NoCopy{value: 30u8});
        assert!(swap_result.is_ok());

        let old_cargo: NoCopy;
        (n, old_cargo) = swap_result.unwrap();
        assert_eq!(1, old_cargo.value);

        total = n.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo.value;
                TraverseAction::Continue
            }
        );

        assert_eq!(52u8, total);
    }

    #[test]
    fn node_swap_cargo_root() {

        #[derive(Debug)]
        struct NoCopy {
            value: u8,
        }

        let mut n = Node::new(NoCopy{value: 10});
        let added_path = n.add_cargo_under(&vec![], NoCopy{value: 1}).unwrap();
        n.add_cargo_under(&vec![], NoCopy{value: 7}).unwrap();

        n.add_cargo_under(&added_path, NoCopy{value: 2}).unwrap();
        n.add_cargo_under(&added_path, NoCopy{value: 3}).unwrap();

        let mut total = n.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo.value;
                TraverseAction::Continue
            }
        );

        assert_eq!(23u8, total);

        let swap_result = Node::swap_cargo(n, &vec![], NoCopy{value: 30u8});
        assert!(swap_result.is_ok());

        let old_cargo: NoCopy;
        (n, old_cargo) = swap_result.unwrap();
        assert_eq!(10, old_cargo.value);

        total = n.traverse(
            0u8,
            |accum, nd, _path| {
                *accum += nd.cargo.value;
                TraverseAction::Continue
            }
        );

        assert_eq!(43u8, total);
    }

    #[test]
    fn node_swap_cargo_wrong_path() {
        let mut n = Node::new('g');
        n.add_cargo_under(&vec![], 'o').unwrap();

        let result = Node::swap_cargo(n, &vec![5], 'a');
        assert!(result.is_err());
        
        let (_, n, old_cargo) = result.unwrap_err();
        assert_eq!(&'g', n.borrow_cargo(&vec![]).unwrap());
        assert_eq!('a', old_cargo);
    }

    #[test]
    fn cargo_with_id_get_next_id() {
        let mut id: usize;
        let mut last_id = CargoWithId::<u8>::get_next_id();

        for _ in 0usize..5 {
            id = CargoWithId::<u8>::get_next_id();
            assert!(last_id < id);
            last_id = id;
        }
    }

    #[test]
    fn cargo_with_id_new() {
        let mut cwi: CargoWithId<bool>;
        let mut last_id = CargoWithId::<u8>::get_next_id();

        for _ in 0usize..5 {
            cwi = CargoWithId::new(true);
            assert!(last_id < cwi.id);
            last_id = cwi.id;
        }
    }

    #[test]
    fn cargo_with_id_clone() {
        let c1 = CargoWithId::new(25u8);
        let c2 = c1.clone();

        assert_eq!(c1.subcargo, c2.subcargo);
        assert_ne!(c1.id, c2.id);
    }

    #[test]
    fn node_with_id_clone() {
        let n1 = Node::new_with_id(25u8);
        let n2 = n1.clone();

        assert_eq!(n1.cargo.subcargo, n2.cargo.subcargo);
        assert_ne!(n1.get_id(), n2.get_id());
    }

    #[test]
    fn node_with_id_add_cargo_under_with_id() {
        let mut n = Node::new_with_id(0u8);
        let id: usize;
        let path: Vec<usize>;

        let result = n.add_cargo_under_with_id(&vec![], 1);
        assert!(result.is_ok());

        (path, id) = result.unwrap();
        assert_eq!(vec![0], path);
        
        let crg = n.borrow_cargo(&vec![0]).unwrap();
        assert_eq!(crg.id, id);
    }

    #[test]
    fn node_with_id_add_cargo_under_with_id_wrong_path() {
        let mut n = Node::new_with_id(0u8);
        let crg: u8;

        let result = n.add_cargo_under_with_id(&vec![4, 7], 1u8);
        assert!(result.is_err());

        (_, crg) = result.unwrap_err();
        assert_eq!(1u8, crg);
    }

    #[test]
    fn node_with_id_add_cargo_after_with_id() {
        let mut n = Node::new_with_id(0u8);
        let id: usize;
        let path: Vec<usize>;

        n.add_cargo_under_with_id(&vec![], 1).unwrap();
        let result = n.add_cargo_after_with_id(&vec![0], 2);

        (path, id) = result.unwrap();
        assert_eq!(vec![1], path);
        
        let crg = n.borrow_cargo(&vec![1]).unwrap();
        assert_eq!(crg.id, id);
    }

    #[test]
    fn node_with_id_add_cargo_after_with_id_wrong_path() {
        let mut n = Node::new_with_id(0u8);
        let crg: u8;

        n.add_cargo_under_with_id(&vec![], 1).unwrap();
        let result = n.add_cargo_after_with_id(&vec![4], 2u8);
        assert!(result.is_err());

        (_, crg) = result.unwrap_err();
        assert_eq!(2u8, crg);
    }

    #[test]
    fn node_with_id_add_cargo_before_with_id() {
        let mut n = Node::new_with_id(0u8);
        let id: usize;
        let path: Vec<usize>;

        n.add_cargo_under_with_id(&vec![], 1).unwrap();
        let result = n.add_cargo_before_with_id(&vec![0], 2);

        (path, id) = result.unwrap();
        assert_eq!(vec![0], path);
        
        let crg = n.borrow_cargo(&vec![0]).unwrap();
        assert_eq!(crg.id, id);
    }

    #[test]
    fn node_with_id_add_cargo_before_with_id_wrong_path() {
        let mut n = Node::new_with_id(0u8);
        let crg: u8;

        n.add_cargo_under_with_id(&vec![], 1).unwrap();
        let result = n.add_cargo_before_with_id(&vec![4], 2u8);
        assert!(result.is_err());

        (_, crg) = result.unwrap_err();
        assert_eq!(2u8, crg);
    }

    #[test]
    fn node_with_id_borrow_cargo_get_path_by_id() {
        let mut n = Node::new_with_id(10);
        let root_path = vec![];
        n.add_cargo_under_with_id(&root_path, 11).unwrap();
        n.add_cargo_under_with_id(&root_path, 12).unwrap();
        let new_id = n.add_cargo_under_with_id(&vec![1], 13).unwrap().1;

        let result = n.borrow_cargo_get_path_by_id(&new_id);
        assert!(result.is_ok());

        let (&found_cargo, found_path) = result.unwrap();
        assert_eq!(13, found_cargo);
        assert_eq!(vec![1, 0], found_path);
    }

    #[test]
    fn node_with_id_borrow_cargo_get_path_by_wrong_id() {
        let mut n = Node::new_with_id(10);
        let root_path = vec![];
        n.add_cargo_under_with_id(&root_path, 11).unwrap();
        n.add_cargo_under_with_id(&root_path, 12).unwrap();
        let new_id = n.add_cargo_under_with_id(&vec![1], 13).unwrap().1;

        let result = n.borrow_cargo_get_path_by_id(&(new_id + 20));
        assert!(result.is_err());
        assert_eq!(PathError::InputIdNotFound, result.unwrap_err());
    }

    #[test]
    fn node_with_id_borrow_cargo_by_id() {
        let mut n = Node::new_with_id(10);
        let root_path = vec![];
        n.add_cargo_under_with_id(&root_path, 11).unwrap();
        n.add_cargo_under_with_id(&root_path, 12).unwrap();
        let new_id = n.add_cargo_under_with_id(&vec![1], 13).unwrap().1;

        let result = n.borrow_cargo_by_id(&new_id);
        assert!(result.is_ok());

        let &found_cargo = result.unwrap();
        assert_eq!(13, found_cargo);
    }

    // Testing some assumptions about vector comparisons.
    mod vec_partialeq {
        #[test]
        fn vec_same_len() {
            let v1:Vec<usize> = vec![1, 2, 3, 1];
            let v2:Vec<usize> = vec![1, 2, 4, 0];

            assert!(v1 < v2);
        }

        #[test]
        fn vec_unequal_size() {
            let v1:Vec<usize> = vec![8, 9];
            let v2:Vec<usize> = vec![8, 8, 10];

            assert!(v1 > v2);
        }

        #[test]
        fn vec_unequal_size_same_elements() {
            let v1:Vec<usize> = vec![8, 9];
            let v2:Vec<usize> = vec![8, 9, 0];

            assert!(v1 < v2);
        }
    }
}
