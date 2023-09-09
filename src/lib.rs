pub struct Node<C> {
    cargo: C,
    children: Vec<Node<C>>,
}

#[derive(PartialEq)]
#[derive(Debug)]
pub enum PathResult {
    Found(Vec<usize>),
    RequestedPathNotAvailable,
    InputPathNotFound,
    ProcessError,
}
impl PathResult {
    pub fn is_found(&self) -> bool {
        match self {
            PathResult::Found(_) => true,
            _ => false,
        }
    }

    pub fn unwrap(self) -> Vec<usize> {
        match self {
            PathResult::Found(path) => path,
            _ => panic!("The unwrap() method musn't be called on a PathResult that's not an Found variant. Check using the is_found() method first."),
        }
    }
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

    pub fn get_next_path(&self, path: &Vec<usize>) -> PathResult {
        let mut return_path = path.clone();

        match self.borrow_node_by_path(&return_path) {
            None => PathResult::InputPathNotFound,
            Some(nd) => {
                if nd.children.len() > 0 {
                    return_path.push(0);
                    PathResult::Found(return_path)
                } else {
                    // Repeat this logic in a loop in order to find the next sibling
                    // of the path node or of a parent that has one.

                    let mut next_node_index: usize;

                    loop {
                        if return_path.len() == 0 {
                            break PathResult::RequestedPathNotAvailable;
                        }

                        next_node_index = return_path.pop().unwrap() + 1;

                        match self.borrow_node_by_path(&return_path) {
                            None => break PathResult::ProcessError,
                            Some(parent) => {
                                if next_node_index < parent.children.len() {
                                    return_path.push(next_node_index);
                                    break PathResult::Found(return_path);
                                }
                            },
                        }
                    }
                }
            },
        }
    }

    pub fn add_cargo_under_path(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, C> {
        let mut return_path = path.clone();
        let borrowed = self.borrow_mut_node_by_path(path);

        match borrowed {
            None => Err(cargo),
            Some(nd) =>  {
                let ix = nd.children.len();
                return_path.push(ix);
                nd.children.push(Node::new(cargo));

                Ok(return_path)
            },
        }
    }

    pub fn add_cargo_after_path(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, C> {
        if path.len() == 0 {
            return Err(cargo);
        }

        let mut return_path = path.clone();
        let last_path = return_path.pop().unwrap() + 1;

        let borrowed = self.borrow_mut_node_by_path(&return_path);

        match borrowed {
            None => Err(cargo),
            Some(nd) =>  {
                if last_path > nd.children.len() {
                    Err(cargo)
                } else {
                    nd.children.insert(last_path, Node::new(cargo));
                    return_path.push(last_path);

                    Ok(return_path)
                }
            },
        }
    }

    pub fn add_cargo_before_path(&mut self, path: &Vec<usize>, cargo: C) -> Result<Vec<usize>, C> {
        if path.len() == 0 {
            return Err(cargo);
        }

        let mut return_path = path.clone();
        let last_path = return_path.pop().unwrap();

        let borrowed = self.borrow_mut_node_by_path(&return_path);

        match borrowed {
            None => Err(cargo),
            Some(nd) =>  {
                if last_path > nd.children.len() {
                    Err(cargo)
                } else {
                    nd.children.insert(last_path, Node::new(cargo));
                    return_path.push(last_path);

                    Ok(return_path)
                }
            },
        }
    }

    pub fn borrow_cargo_by_path(&self, path: &Vec<usize>) -> Option<&C> {
        let borrowed = self.borrow_node_by_path(path);

        match borrowed {
            None => None,
            Some(nd) => Some(&nd.cargo),
        }
    }

    pub fn borrow_mut_cargo_by_path(&mut self, path: &Vec<usize>) -> Option<&mut C> {
        let borrowed = self.borrow_mut_node_by_path(path);

        match borrowed {
            None => None,
            Some(nd) => Some(&mut nd.cargo),
        }
    }

    fn borrow_node_by_path(&self, path: &Vec<usize>) -> Option<&Node<C>> {
        let mut outcome: Option<&Node<C>> = Some(self);
        let mut pathix = 0usize;
        let path_len = path.len();
        let mut nd: &Node<C>;

        while pathix < path_len {
            nd = outcome.unwrap();

            if path[pathix] < nd.children.len() {
                outcome = Some(&nd.children[path[pathix]]);
            } else {
                outcome = None;
                break;
            }

            pathix += 1;
        }

        outcome
    }

    fn borrow_mut_node_by_path(&mut self, path: &Vec<usize>) -> Option<&mut Node<C>> {
        let mut outcome = Some(self);
        let mut pathix = 0usize;
        let path_len = path.len();
        let mut nd: &mut Node<C>;

        while pathix < path_len {
            nd = outcome.unwrap();

            if path[pathix] < nd.children.len() {
                outcome = Some(&mut nd.children[path[pathix]]);
            } else {
                outcome = None;
                break;
            }

            pathix += 1;
        }

        outcome
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

        let mut borrowed: Option<&Node<u8>>;

        borrowed = n.borrow_node_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_some());
        assert_eq!(0, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![1]);
        assert!(borrowed.is_some());
        assert_eq!(2, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![2]);
        assert!(borrowed.is_some());
        assert_eq!(5, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![3]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_node_by_path(&vec![1, 0]);
        assert!(borrowed.is_some());
        assert_eq!(3, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![1, 1]);
        assert!(borrowed.is_some());
        assert_eq!(4, borrowed.unwrap().cargo);

        borrowed = n.borrow_node_by_path(&vec![1, 2]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_node_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_none());
    }

    #[test]
    fn node_borrow_mut_node_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Option<&mut Node<u8>>;

        borrowed = n.borrow_mut_node_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_some());
        assert_eq!(0, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![1]);
        assert!(borrowed.is_some());
        assert_eq!(2, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![2]);
        assert!(borrowed.is_some());
        assert_eq!(5, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![3]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_mut_node_by_path(&vec![1, 0]);
        assert!(borrowed.is_some());
        assert_eq!(3, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![1, 1]);
        assert!(borrowed.is_some());
        assert_eq!(4, borrowed.unwrap().cargo);

        borrowed = n.borrow_mut_node_by_path(&vec![1, 2]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_mut_node_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_none());
    }

    #[test]
    fn node_borrow_cargo_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Option<&u8>;

        borrowed = n.borrow_cargo_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_some());
        assert_eq!(&0, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![1]);
        assert!(borrowed.is_some());
        assert_eq!(&2, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![2]);
        assert!(borrowed.is_some());
        assert_eq!(&5, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![3]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_cargo_by_path(&vec![1, 0]);
        assert!(borrowed.is_some());
        assert_eq!(&3, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![1, 1]);
        assert!(borrowed.is_some());
        assert_eq!(&4, borrowed.unwrap());

        borrowed = n.borrow_cargo_by_path(&vec![1, 2]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_cargo_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_none());
    }

    #[test]
    fn node_borrow_mut_cargo_by_path() {
        let mut n = Node::new(0u8);
        n.children.push(Node::new(1u8));
        n.children.push(Node::new(2u8));
        n.children[1].children.push(Node::new(3u8));
        n.children[1].children.push(Node::new(4u8));
        n.children.push(Node::new(5u8));

        let mut borrowed: Option<&mut u8>;

        borrowed = n.borrow_mut_cargo_by_path(&Vec::<usize>::new());
        assert!(borrowed.is_some());
        assert_eq!(&mut 0, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1]);
        assert!(borrowed.is_some());
        assert_eq!(&mut 2, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![2]);
        assert!(borrowed.is_some());
        assert_eq!(&mut 5, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![3]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 0]);
        assert!(borrowed.is_some());
        assert_eq!(&mut 3, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 1]);
        assert!(borrowed.is_some());
        assert_eq!(&mut 4, borrowed.unwrap());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 2]);
        assert!(borrowed.is_none());

        borrowed = n.borrow_mut_cargo_by_path(&vec![1, 1, 0]);
        assert!(borrowed.is_none());
    }

    #[test]
    fn node_add_cargo_under_path() {
        let mut n = Node::new(0u8);
        let mut result: Result<Vec<usize>, u8>;

        result = n.add_cargo_under_path(&vec![], 1);
        assert!(result.is_ok());
        assert_eq!(vec![0], result.unwrap());

        result = n.add_cargo_under_path(&vec![], 2);
        assert!(result.is_ok());
        assert_eq!(vec![1], result.unwrap());

        result = n.add_cargo_under_path(&vec![0], 3);
        assert!(result.is_ok());
        assert_eq!(vec![0, 0], result.unwrap());

        result = n.add_cargo_under_path(&vec![0], 4);
        assert!(result.is_ok());
        assert_eq!(vec![0, 1], result.unwrap());

        let borrowed = n.borrow_cargo_by_path(&vec![0, 1]);
        assert!(borrowed.is_some());
        assert_eq!(&4, borrowed.unwrap());

        result = n.add_cargo_under_path(&vec![50], 99);
        assert!(result.is_err());
        assert_eq!(99, result.unwrap_err());

        result = n.add_cargo_under_path(&vec![0, 1, 1], 99);
        assert!(result.is_err());
        assert_eq!(99, result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_after_path_empty() {
        let mut n = Node::new(0i8);
        let result: Result<Vec<usize>, i8>;

        result = n.add_cargo_after_path(&vec![], -38);
        assert!(result.is_err());
        assert_eq!(-38, result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_after_path() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, i8>;
        let mut result_path: Vec<usize>;

        result = n.add_cargo_after_path(&vec![0], 1);
        assert!(result.is_err());
        assert_eq!(1, result.unwrap_err());

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
        let result: Result<Vec<usize>, i8>;

        result = n.add_cargo_before_path(&vec![], -38);
        assert!(result.is_err());
        assert_eq!(-38, result.unwrap_err());
    }

    #[test]
    fn node_add_cargo_before_path() {
        let mut n = Node::new(0i8);
        let mut result: Result<Vec<usize>, i8>;
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
        assert_eq!(5, result.unwrap_err());
    }

    #[test]
    fn node_get_next_path_on_lone_root() {
        let n = Node::new(0u8);
        assert_eq!(PathResult::RequestedPathNotAvailable, n.get_next_path(&vec![]));
    }

    #[test]
    fn node_get_next_path_input_not_found() {
        let n = Node::new(0u8);
        assert_eq!(PathResult::InputPathNotFound, n.get_next_path(&vec![5]));
    }

    #[test]
    fn node_get_next_path_from_last() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        assert_eq!(PathResult::RequestedPathNotAvailable, n.get_next_path(&vec![1]));
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
        assert!(path_result.is_found());
        let next_path = path_result.unwrap();
        assert_eq!(vec![1], next_path);
        assert_eq!(&2, n.borrow_cargo_by_path(&next_path).unwrap());
    }

    #[test]
    fn node_get_next_path_root_to_child() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        assert_eq!(PathResult::Found(vec![0]), n.get_next_path(&vec![]));
    }

    #[test]
    fn node_get_next_path_non_root_to_child() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_after_path(&vec![1], 4).unwrap();
        assert_eq!(PathResult::Found(vec![1, 0]), n.get_next_path(&vec![1]));
    }

    #[test]
    fn node_get_next_path_non_child_to_parents_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_after_path(&vec![1], 4).unwrap();
        assert_eq!(PathResult::Found(vec![2]), n.get_next_path(&vec![1, 0]));
    }

    #[test]
    fn node_get_next_path_non_child_to_grandparents_sibling() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1, 0], 4).unwrap();
        n.add_cargo_after_path(&vec![1], 5).unwrap();
        assert_eq!(PathResult::Found(vec![2]), n.get_next_path(&vec![1, 0, 0]));
    }

    #[test]
    fn node_get_next_path_from_last_is_grandchild() {
        let mut n = Node::new(0u8);
        n.add_cargo_under_path(&vec![], 1).unwrap();
        n.add_cargo_after_path(&vec![0], 2).unwrap();
        n.add_cargo_under_path(&vec![1], 3).unwrap();
        n.add_cargo_under_path(&vec![1, 0], 4).unwrap();
        assert_eq!(PathResult::RequestedPathNotAvailable, n.get_next_path(&vec![1, 0, 0]));
    }
}
