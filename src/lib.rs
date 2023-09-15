#[derive(Debug)]
#[derive(PartialEq)]
pub struct Node<C> {
    cargo: C,
    children: Vec<Node<C>>,
}
impl<C> Node<C> {
    pub fn new(cargo: C) -> Node<C> {
        Node {
            cargo: cargo,
            children: Vec::<Node<C>>::new(),
        }
    }

    pub fn get_first_path(&self) -> Vec<usize> {
        vec![]
    }

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

    pub fn get_next_path(&self, path: &Vec<usize>) -> Result<Vec<usize>, PathError> {
        let mut result_path = path.clone();

        match self.borrow_node_by_path(&result_path) {
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

                        match self.borrow_node_by_path(&result_path) {
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

    pub fn get_previous_path(&self, path: &Vec<usize>) -> Result<Vec<usize>, PathError> {
        if path.len() == 0 {
            return Err(PathError::RequestedPathNotAvailable);
        }

        let mut result_path = path.clone();

        match self.borrow_node_by_path(&result_path) {
            Err(err) => Err(err),
            Ok(_) => {
                let input_index = result_path.pop().unwrap();
                let mut children_count: usize;

                if input_index > 0 {
                    result_path.push(input_index - 1);

                    // Descend do deepest last grandchild of this node.
                    loop {
                        match self.borrow_node_by_path(&result_path) {
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

    pub fn add_cargo_under_path(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, (PathError, C)> {
        let mut result_path = path.clone();
        let borrowed = self.borrow_mut_node_by_path(path);

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

    pub fn add_cargo_after_path(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, (PathError, C)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, cargo));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap() + 1;

        let borrowed = self.borrow_mut_node_by_path(&result_path);

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

    pub fn add_cargo_before_path(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, (PathError, C)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, cargo));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap();

        let borrowed = self.borrow_mut_node_by_path(&result_path);

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

    pub fn extract_node_by_path(&mut self, path: &Vec<usize>) -> Result<Node<C>, PathError> {
        if path.len() == 0 {
            return Err(PathError::InputPathNotFitForOperation);
        }

        let mut parent_path = path.clone();
        let last_index = parent_path.pop().unwrap();
        let parent_result = self.borrow_mut_node_by_path(&parent_path);

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

    pub fn add_node_under_path(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Vec<usize>, (PathError, Node<C>)> {
        let mut result_path = path.clone();
        let borrowed = self.borrow_mut_node_by_path(path);

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

    pub fn add_node_after_path(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Vec<usize>, (PathError, Node<C>)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, node));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap() + 1;

        let borrowed = self.borrow_mut_node_by_path(&result_path);

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

    pub fn add_node_before_path(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Vec<usize>, (PathError, Node<C>)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, node));
        }

        let mut result_path = path.clone();
        let last_path = result_path.pop().unwrap();

        let borrowed = self.borrow_mut_node_by_path(&result_path);

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

    pub fn swap_node_by_path(&mut self, path: &Vec<usize>, node: Node<C>) -> Result<Node<C>, (PathError, Node<C>)> {
        if path.len() == 0 {
            return Err((PathError::InputPathNotFitForOperation, node));
        }

        let mut parent_path = path.clone();
        let last_path = parent_path.pop().unwrap();

        let borrowed = self.borrow_mut_node_by_path(&parent_path);

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

    pub fn borrow_cargo_by_path(&self, path: &Vec<usize>) -> Result<&C, PathError> {
        let borrowed = self.borrow_node_by_path(path);

        match borrowed {
            Ok(nd) => Ok(&nd.cargo),
            Err(err) => Err(err),
        }
    }

    pub fn borrow_mut_cargo_by_path(&mut self, path: &Vec<usize>) -> Result<&mut C, PathError> {
        let borrowed = self.borrow_mut_node_by_path(path);

        match borrowed {
            Ok(nd) => Ok(&mut nd.cargo),
            Err(err) => Err(err),
        }
    }

    pub fn has_path(&self, path: &Vec<usize>) -> bool {
        self.borrow_node_by_path(path).is_ok()
    }

    pub fn iter(&self) -> NodeIterator<C> {
        NodeIterator::new(self)
    }

    pub fn traverse<Accum, CallBack>(&mut self, mut init: Accum, mut call_back: CallBack) -> Accum
    where CallBack: FnMut(&mut Accum, &mut C, &Vec<usize>) -> bool {
        let mut current_path = self.get_first_path();
        let mut current_cargo: &mut C;

        loop {
            current_cargo = self.borrow_mut_cargo_by_path(&current_path)
                .expect("While traversing, borrowing a node's cargo should never yield Result::Err.");

            if !(call_back)(&mut init, current_cargo, &current_path) {
                break;
            }

            current_path = match self.get_next_path(&current_path) {
                Ok(p) => p,
                _ => break,
            }
        }

        init
    }

    fn borrow_node_by_path(&self, path: &Vec<usize>) -> Result<&Node<C>, PathError> {
        let mut outcome = Ok(self);
        let mut pathix = 0usize;
        let path_len = path.len();
        let mut nd: &Node<C>;

        while pathix < path_len {
            nd = outcome.unwrap();

            if path[pathix] < nd.children.len() {
                outcome = Ok(&nd.children[path[pathix]]);
            } else {
                outcome = Err(PathError::InputPathNotFound);
                break;
            }

            pathix += 1;
        }

        outcome
    }

    fn borrow_mut_node_by_path(&mut self, path: &Vec<usize>) -> Result<&mut Node<C>, PathError> {
        let mut outcome = Ok(self);
        let mut pathix = 0usize;
        let path_len = path.len();
        let mut nd: &mut Node<C>;

        while pathix < path_len {
            nd = outcome.unwrap();

            if path[pathix] < nd.children.len() {
                outcome = Ok(&mut nd.children[path[pathix]]);
            } else {
                outcome = Err(PathError::InputPathNotFound);
                break;
            }

            pathix += 1;
        }

        outcome
    }
}

#[derive(PartialEq)]
#[derive(Debug)]
pub enum PathError {
    InputPathNotFound,
    InputPathNotFitForOperation,
    RequestedPathNotAvailable,
    ProcessError,
}

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
            true => Some(self.root.borrow_cargo_by_path(&self.current_path).unwrap()),
            false => None,
        }
    }
}
impl<'it, C> DoubleEndedIterator for NodeIterator<'it, C> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let has_next = self.set_next_path(false);

        match has_next {
            true => Some(self.root.borrow_cargo_by_path(&self.back_current_path).unwrap()),
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
    fn node_borrow_node_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&Node<u8>, PathError>;

        borrowed = n.borrow_node_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_ok());
        assert_eq!(0, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(2, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(5, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_node_by_path(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(3, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(4, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_node_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_borrow_mut_node_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&mut Node<u8>, PathError>;

        borrowed = n.borrow_mut_node_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_ok());
        assert_eq!(0, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(2, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(5, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_node_by_path(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(3, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(4, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_node_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_borrow_cargo_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&u8, PathError>;

        borrowed = n.borrow_cargo_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_ok());
        assert_eq!(&0, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(&2, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(&5, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_cargo_by_path(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(&3, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(&4, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_cargo_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_borrow_mut_cargo_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Result<&mut u8, PathError>;

        // Check if we can read twice.
        for _i in 0..2 {
            borrowed = n.borrow_mut_cargo_by_path(&Vec::<usize>::new());
            assert!(borrowed.is_ok());
            assert_eq!(&mut 0, borrowed.unwrap());
        }

        borrowed = n.borrow_mut_cargo_by_path(&vec![1]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 2, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![2]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 5, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![3]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 0]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 3, borrowed.unwrap());

        // Check if we can change the cargo.
        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 1]);
        assert!(borrowed.is_ok());
        let unwrapped = borrowed.unwrap();
        assert_eq!(&mut 4, unwrapped);
        *unwrapped = 40;
        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(&mut 40, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 2]);
        assert!(borrowed.is_err());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_err());
    }

    #[test]
    fn node_add_cargo_under_path() {
        let mut n = Node::new(0u8);
        let mut result: Result<Vec<usize>, (PathError, u8)>;

        result = n.add_cargo_under_path(&vec![], 1);
        assert!(result.is_ok());
        assert_eq!(vec![0], result.unwrap());

        result = n.add_cargo_under_path(&vec![], 2);
        assert!(result.is_ok());
        assert_eq!(vec![1], result.unwrap());
        assert_eq!(&2, n.borrow_cargo_by_path(&vec![1]).unwrap());

        result = n.add_cargo_under_path(&vec![0], 3);
        assert!(result.is_ok());
        assert_eq!(vec![0, 0], result.unwrap());

        result = n.add_cargo_under_path(&vec![0], 4);
        assert!(result.is_ok());
        assert_eq!(vec![0, 1], result.unwrap());

        let borrowed = n.borrow_cargo_by_path(&vec![0, 1]);
        assert!(borrowed.is_ok());
        assert_eq!(&4, borrowed.unwrap());

        result = n.add_cargo_under_path(&vec![50], 99);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound,99), result.unwrap_err());

        result = n.add_cargo_under_path(&vec![0, 1, 1], 99);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound,99), result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_after_path_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, (PathError, i8)>;

        result = n.add_cargo_after_path(&vec![], -38);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation, -38), result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_after_path() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, (PathError, i8)>;
        let mut result_path: Vec<usize>;

        result = n.add_cargo_after_path(&vec![0], 1);
        assert!(result.is_err());
        assert_eq!((PathError::RequestedPathNotAvailable, 1), result.unwrap_err());

        n.add_cargo_under_path(&vec![], 1).unwrap();

        result = n.add_cargo_after_path(&vec![0], 2);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&2, n.borrow_cargo_by_path(&result_path).unwrap());

        result = n.add_cargo_after_path(&vec![0], 3);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo_by_path(&result_path).unwrap());
        assert_eq!(&2, n.borrow_cargo_by_path(&vec![2]).unwrap());
    }

    #[test]
    fn node_add_cargo_before_path_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, (PathError, i8)>;

        result = n.add_cargo_before_path(&vec![], -38);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation,-38), result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_before_path() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, (PathError, i8)>;
        let mut result_path: Vec<usize>;

        result = n.add_cargo_before_path(&vec![0], 1);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&1, n.borrow_cargo_by_path(&result_path).unwrap());

        result = n.add_cargo_before_path(&vec![0], 2);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&2, n.borrow_cargo_by_path(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo_by_path(&vec![1]).unwrap());

        result = n.add_cargo_before_path(&vec![1], 3);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo_by_path(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo_by_path(&vec![2]).unwrap());

        result = n.add_cargo_before_path(&vec![0, 0], 4);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0, 0], result_path);
        assert_eq!(&4, n.borrow_cargo_by_path(&result_path).unwrap());

        result = n.add_cargo_before_path(&vec![2, 1], 5);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound,5), result.unwrap_err());
    }

    #[test]
    fn node_get_next_path_on_lone_root() {
        let n = Node::new(0u8);
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_next_path(&vec![]));
    }

    #[test]
    fn node_get_next_path_input_not_found() {
        let n = Node::new(0u8);
        assert_eq!(Err(PathError::InputPathNotFound), n.get_next_path(&vec![5]));
    }

    #[test]
    fn node_get_next_path_from_last() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_next_path(&vec![1]));
    }

    #[test]
    #[should_panic]
    fn node_get_next_path_from_last_unwrap() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        let path_result = n.get_next_path(&vec![1]);
        path_result.unwrap();
    }

    #[test]
    fn node_get_next_path_next_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();

        let path_result = n.get_next_path(&vec![0]);
        assert!(path_result.is_ok());
        let next_path = path_result.unwrap();
        assert_eq!(vec![1], next_path);
        assert_eq!(&2, n.borrow_cargo_by_path(&next_path).unwrap());
    }

    #[test]
    fn node_get_next_path_root_to_child() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        assert_eq!(Ok(vec![0]), n.get_next_path(&vec![]));
    }

    #[test]
    fn node_get_next_path_non_root_to_child() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_after_path(&vec![1], 4).unwrap();
        assert_eq!(Ok(vec![1, 0]), n.get_next_path(&vec![1]));
    }

    #[test]
    fn node_get_next_path_non_child_to_parents_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_after_path(&vec![1], 4).unwrap();
        assert_eq!(Ok(vec![2]), n.get_next_path(&vec![1, 0]));
    }

    #[test]
    fn node_get_next_path_non_child_to_grandparents_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1, 0], 4).unwrap();
        n.add_cargo_after_path(&vec![1], 5).unwrap();
        assert_eq!(Ok(vec![2]), n.get_next_path(&vec![1, 0, 0]));
    }

    #[test]
    fn node_get_next_path_from_last_is_grandchild() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1, 0], 4).unwrap();
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_next_path(&vec![1, 0, 0]));
    }

    #[test]
    fn node_get_previous_path_from_unexistent() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1, 0], 4).unwrap();
        assert_eq!(Err(PathError::InputPathNotFound), n.get_next_path(&vec![3, 0, 0]));
    }

    #[test]
    fn node_get_previous_path_from_root() {
        let n = Node::new(String::from("aaa"));
        assert_eq!(Err(PathError::RequestedPathNotAvailable), n.get_previous_path(&vec![]));
    }

    #[test]
    fn node_get_previous_path() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1, 0], 4).unwrap();
        n.add_cargo_after_path(&vec![1], 5).unwrap();
        n.add_cargo_after_path(&vec![2], 6).unwrap();
        n.add_cargo_after_path(&vec![1, 0], 50).unwrap();
        n.add_cargo_under_path(&vec![1, 1], 51).unwrap();
        n.add_cargo_after_path(&vec![1, 1, 0], 52).unwrap();

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
        assert_eq!(&52, n.borrow_cargo_by_path(&previous).unwrap());

        // Descend to last grandchild under previous sibling (bis)
        path_result = n.get_previous_path(&vec![1, 1]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 0, 0], previous);
        assert_eq!(&4, n.borrow_cargo_by_path(&previous).unwrap());

        // Find previous sibling
        path_result = n.get_previous_path(&vec![1, 1, 1]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 1, 0], previous);
        assert_eq!(&51, n.borrow_cargo_by_path(&previous).unwrap());

        // Find previous sibling (bis)
        path_result = n.get_previous_path(&vec![1]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![0], previous);
        assert_eq!(&1, n.borrow_cargo_by_path(&previous).unwrap());

        // Find non-root parent
        path_result = n.get_previous_path(&vec![1, 1, 0]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(vec![1, 1], previous);
        assert_eq!(&50, n.borrow_cargo_by_path(&previous).unwrap());
        
        // Find root parent
        path_result = n.get_previous_path(&vec![0]);
        assert!(path_result.is_ok());
        previous = path_result.unwrap();
        assert_eq!(Vec::<usize>::new(), previous);
        assert_eq!(&0, n.borrow_cargo_by_path(&previous).unwrap());
    }

    #[test]
    fn node_get_last_path_on_lone_root() {
        let n = Node::new('K');
        let result = n.get_last_path();
        assert_eq!(Vec::<usize>::new(), result);
    }

    #[test]
    fn node_get_last_path_on_lone_child() {
        let mut n = Node::new('K');
        n.add_cargo_under_path(&vec![], 'Z').unwrap();
        let result = n.get_last_path();
        assert_eq!(vec![0usize], result);
    }

    #[test]
    fn node_get_last_path_on_first_level() {
        let mut n = Node::new('A');
        n.add_cargo_under_path(&vec![], 'B').unwrap();
        n.add_cargo_under_path(&vec![], 'C').unwrap();
        n.add_cargo_under_path(&vec![], 'D').unwrap();
        let result = n.get_last_path();
        assert_eq!(vec![2usize], result);
        assert_eq!(&'D', n.borrow_cargo_by_path(&vec![2]).unwrap());
    }

    #[test]
    fn node_extract_node_by_path_root() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&n.get_first_path(), 1).unwrap();
        let result = n.extract_node_by_path(&n.get_first_path());
        assert!(result.is_err());
        assert_eq!(PathError::InputPathNotFitForOperation, result.unwrap_err());
    }

    #[test]
    fn node_extract_node_by_path_nonexistent() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&n.get_first_path(), 1).unwrap();
        let result = n.extract_node_by_path(&vec![0, 3]);
        assert!(result.is_err());
        assert_eq!(PathError::InputPathNotFound, result.unwrap_err());
    }

    #[test]
    fn node_extract_node_by_path_lone_leaf() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&n.get_first_path(), 1).unwrap();
        let result = n.extract_node_by_path(&vec![0]);
        assert!(result.is_ok());
        let nd = result.unwrap();
        assert_eq!(1, nd.cargo);
    }

    #[test]
    fn node_extract_node_by_path_lone_non_leaf() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&n.get_first_path(), 1).unwrap();
        n.add_cargo_under_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![0], 3).unwrap();
        let result = n.extract_node_by_path(&vec![0]);
        assert!(result.is_ok());
        let nd = result.unwrap();
        assert_eq!(1, nd.cargo);
        assert!(nd.borrow_cargo_by_path(&vec![1]).is_ok());
    }

    #[test]
    fn node_extract_node_by_path_non_leaf() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 90).unwrap();
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_under_path(&vec![], 91).unwrap();
        n.add_cargo_under_path(&vec![1], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        let result = n.extract_node_by_path(&vec![1]);
        assert!(result.is_ok());
        let nd = result.unwrap();
        assert_eq!(1, nd.cargo);
        assert!(nd.borrow_cargo_by_path(&vec![1]).is_ok());
        assert!(!n.has_path(&vec![2]));
        assert_eq!(&91, n.borrow_cargo_by_path(&vec![1]).unwrap());
    }

    #[test]
    fn node_add_node_under_nonexistent_path() {
        let mut n = Node::new(0u8);
        let n1 = Node::new(1u8);
        let result: Result<Vec<usize>, (PathError, Node<u8>)>;

        result = n.add_node_under_path(&vec![2, 4], n1);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::InputPathNotFound, err);
        assert_eq!(&1u8, bounced_node.borrow_cargo_by_path(&vec![]).unwrap());
    }

    #[test]
    fn node_add_node_under_path() {
        let mut n = Node::new(0u8);
        let n1 = Node::new(1u8);
        let result: Result<Vec<usize>, (PathError, Node<u8>)>;
        let result_path: Vec<usize>;

        result = n.add_node_under_path(&vec![], n1);
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&1, n.borrow_cargo_by_path(&result_path).unwrap());
    }

    #[test]
    fn node_add_node_after_path_empty() {
        let mut n = Node::new(0i8);
        let n1 = Node::new(-38i8);
        let result: Result<Vec<usize>, (PathError, Node<i8>)>;

        result = n.add_node_after_path(&vec![], n1);
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation, Node::new(-38i8)), result.unwrap_err());
    }

    #[test]
    fn node_add_node_after_path() {
        let mut n = Node::new(0i8);
        let n1 = Node::new(1i8);
        let mut result: Result<Vec<usize>, (PathError, Node<i8>)>;
        let mut result_path: Vec<usize>;

        result = n.add_node_after_path(&vec![0], n1);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::RequestedPathNotAvailable, err);
        assert_eq!(Node::new(1i8), bounced_node);

        n.add_node_under_path(&vec![], bounced_node).unwrap();

        result = n.add_node_after_path(&vec![0], Node::new(2i8));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&2, n.borrow_cargo_by_path(&result_path).unwrap());

        result = n.add_node_after_path(&vec![0], Node::new(3));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo_by_path(&result_path).unwrap());
        assert_eq!(&2, n.borrow_cargo_by_path(&vec![2]).unwrap());
    }

    #[test]
    fn node_add_node_before_path_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, (PathError, Node<i8>)>;

        result = n.add_node_before_path(&vec![], Node::new(-38));
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFitForOperation, Node::new(-38)), result.unwrap_err());
    }

    #[test]
    fn node_add_node_before_path() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, (PathError, Node<i8>)>;
        let mut result_path: Vec<usize>;

        result = n.add_node_before_path(&vec![0], Node::new(1));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&1, n.borrow_cargo_by_path(&result_path).unwrap());

        result = n.add_node_before_path(&vec![0], Node::new(2));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0], result_path);
        assert_eq!(&2, n.borrow_cargo_by_path(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo_by_path(&vec![1]).unwrap());

        result = n.add_node_before_path(&vec![1], Node::new(3));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![1], result_path);
        assert_eq!(&3, n.borrow_cargo_by_path(&result_path).unwrap());
        assert_eq!(&1, n.borrow_cargo_by_path(&vec![2]).unwrap());

        result = n.add_node_before_path(&vec![0, 0], Node::new(4));
        assert!(result.is_ok());
        result_path = result.unwrap();
        assert_eq!(vec![0, 0], result_path);
        assert_eq!(&4, n.borrow_cargo_by_path(&result_path).unwrap());

        result = n.add_node_before_path(&vec![2, 1], Node::new(5));
        assert!(result.is_err());
        assert_eq!((PathError::InputPathNotFound, Node::new(5)), result.unwrap_err());
    }
    
    #[test]
    fn node_swap_node_by_path_root() {
        let mut n = Node::new(0u8);
        let to_swap = Node::new(1u8);
        let result = n.swap_node_by_path(&vec![], to_swap);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::InputPathNotFitForOperation, err);
        assert_eq!(&1u8, bounced_node.borrow_cargo_by_path(&vec![]).unwrap());
    }

    #[test]
    fn node_swap_node_by_path_unexistent() {
        let mut n = Node::new(0u8);
        let to_swap = Node::new(1u8);
        let result = n.swap_node_by_path(&vec![8], to_swap);
        assert!(result.is_err());
        let (err, bounced_node) = result.unwrap_err();
        assert_eq!(PathError::InputPathNotFound, err);
        assert_eq!(&1u8, bounced_node.borrow_cargo_by_path(&vec![]).unwrap());
    }
    
    #[test]
    fn node_swap_node_by_path() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_under_path(&vec![], 2).unwrap();
        n.add_cargo_under_path(&vec![], 3).unwrap();
        n.add_cargo_under_path(&vec![1], 20).unwrap();
        n.add_cargo_under_path(&vec![1], 21).unwrap();
        n.add_cargo_under_path(&vec![1], 22).unwrap();

        let mut to_swap = Node::new(9u8);
        to_swap.add_cargo_under_path(&vec![], 90).unwrap();
        to_swap.add_cargo_under_path(&vec![], 91).unwrap();
        to_swap.add_cargo_under_path(&vec![], 92).unwrap();
        to_swap.add_cargo_under_path(&vec![], 93).unwrap();

        let result = n.swap_node_by_path(&vec![1], to_swap);
        assert!(result.is_ok());
        let removed = result.unwrap();

        assert_eq!(4, n.borrow_node_by_path(&vec![1]).unwrap().children.len());
        assert_eq!(3, removed.children.len());

        assert_eq!(&9, n.borrow_cargo_by_path(&vec![1]).unwrap());
        assert_eq!(&93, n.borrow_cargo_by_path(&vec![1, 3]).unwrap());
        assert_eq!(&2, removed.borrow_cargo_by_path(&vec![]).unwrap());
        assert_eq!(&22, removed.borrow_cargo_by_path(&vec![2]).unwrap());
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
        n.add_cargo_under_path(&vec![], 'B').unwrap();
        n.add_cargo_under_path(&vec![], 'C').unwrap();
        n.add_cargo_under_path(&vec![], 'D').unwrap();
        n.add_cargo_under_path(&vec![2], 'E').unwrap();
        n.add_cargo_under_path(&vec![2], 'F').unwrap();
        n.add_cargo_under_path(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under_path(&vec![], 'H').unwrap();

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
        n.add_cargo_under_path(&vec![], 'B').unwrap();
        n.add_cargo_under_path(&vec![], 'C').unwrap();
        n.add_cargo_under_path(&vec![], 'D').unwrap();
        n.add_cargo_under_path(&vec![2], 'E').unwrap();
        n.add_cargo_under_path(&vec![2], 'F').unwrap();
        n.add_cargo_under_path(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under_path(&vec![], 'H').unwrap();

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
        n.add_cargo_under_path(&vec![], 'B').unwrap();
        n.add_cargo_under_path(&vec![], 'C').unwrap();
        n.add_cargo_under_path(&vec![], 'D').unwrap();
        n.add_cargo_under_path(&vec![2], 'E').unwrap();
        n.add_cargo_under_path(&vec![2], 'F').unwrap();
        n.add_cargo_under_path(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under_path(&vec![], 'H').unwrap();

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
        n.add_cargo_under_path(&vec![], 'B').unwrap();
        n.add_cargo_under_path(&vec![], 'C').unwrap();
        n.add_cargo_under_path(&vec![], 'D').unwrap();
        n.add_cargo_under_path(&vec![2], 'E').unwrap();
        n.add_cargo_under_path(&vec![2], 'F').unwrap();
        n.add_cargo_under_path(&vec![2, 1], 'G').unwrap();
        n.add_cargo_under_path(&vec![], 'H').unwrap();

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
            |acc, crg, _path| {
                *acc += *crg;
                true
            }
        );

        assert_eq!(38, outcome);
    }

    #[test]
    fn node_traverse_and_change() {
        let mut n = Node::new(0);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_under_path(&vec![], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1], 4).unwrap();
        n.add_cargo_under_path(&vec![], 5).unwrap();

        let mut outcome = n.traverse(
            0,
            |acc, crg, path| {
                if path.len() == 1 {
                    *crg *= 2;
                    *acc += 1;
                }

                true
            }
        );

        assert_eq!(3, outcome);

        outcome = n.traverse(
            0,
            |acc, crg, _path| {
                *acc += *crg;
                true
            }
        );

        assert_eq!(23, outcome);
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
