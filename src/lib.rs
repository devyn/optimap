use std::{
    cmp::Ordering,
    mem::{ManuallyDrop, MaybeUninit},
};

#[derive(Debug, Clone)]
pub struct Optimap<K, V, const B: usize> {
    root: Option<Box<Node<K, V, B>>>,
}

struct Node<K, V, const B: usize> {
    // All of the arrays are guaranteed initialized up to `length` items, where length <= B
    length: usize,
    keys: [MaybeUninit<K>; B],
    // edges is initialized up to min(length + 1, B)
    edges: [MaybeUninit<Option<Box<Node<K, V, B>>>>; B],
    // If length == B, this is initialized too
    right_edge: MaybeUninit<Option<Box<Node<K, V, B>>>>,
    values: [MaybeUninit<V>; B],
}

impl<K, V, const B: usize> std::fmt::Debug for Node<K, V, B>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("length", &self.length)
            .field("keys", &unsafe {
                std::mem::transmute::<_, &[K]>(&self.keys[0..self.length])
            })
            .field("edges", &unsafe {
                std::mem::transmute::<_, &[Option<Box<Node<K, V, B>>>]>(
                    &self.edges[0..(self.length + 1).min(B)],
                )
            })
            .field(
                "right_edge",
                &if self.length == B {
                    unsafe { self.right_edge.assume_init_ref() }
                } else {
                    &None
                },
            )
            .field("values", &unsafe {
                std::mem::transmute::<_, &[V]>(&self.values[0..self.length])
            })
            .finish()
    }
}

impl<K, V, const B: usize> Optimap<K, V, B>
where
    K: Ord,
{
    pub const fn new() -> Optimap<K, V, B> {
        Optimap { root: None }
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.root.as_ref().and_then(|root| root.search(key))
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let root = self.root.get_or_insert_with(|| Box::new(Node::new()));
        match root.insert(key, value) {
            InsertResult::Inserted(result) => result,
            InsertResult::Overflow(key, value) => {
                // The root was too big, so we have to do a root split
                let (split_key, split_value, mut right_node) = root.split();
                let mut left_node = self.root.take().expect("root was not set");
                match if key < split_key {
                    left_node.insert(key, value)
                } else {
                    right_node.insert(key, value)
                } {
                    InsertResult::Inserted(_) => (),
                    InsertResult::Overflow(_, _) => {
                        panic!("Shouldn't be possible to overflow after root split");
                    }
                }
                self.root = Some(Box::new(Node::new_root(
                    split_key,
                    split_value,
                    left_node,
                    right_node,
                )));
                None
            }
        }
    }
}

impl<K, V, const B: usize> Clone for Node<K, V, B>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        unsafe {
            let mut new_node = Node::new();

            // SAFETY: only touching data guaranteed initialized by `length`
            for (dst, src) in new_node.keys.iter_mut().zip(&self.keys).take(self.length) {
                dst.write(src.assume_init_ref().clone());
            }
            for (dst, src) in new_node
                .edges
                .iter_mut()
                .zip(&self.edges)
                .take(self.length + 1)
            {
                dst.write(src.assume_init_ref().clone());
            }
            if self.length == B {
                new_node
                    .right_edge
                    .write(self.right_edge.assume_init_ref().clone());
            }
            for (dst, src) in new_node
                .values
                .iter_mut()
                .zip(&self.values)
                .take(self.length)
            {
                dst.write(src.assume_init_ref().clone());
            }

            new_node.length = self.length;

            new_node
        }
    }
}

impl<K, V, const B: usize> Node<K, V, B> {
    const fn new() -> Self {
        unsafe {
            Node {
                length: 0,
                keys: MaybeUninit::uninit().assume_init(),
                edges: MaybeUninit::zeroed().assume_init(),
                right_edge: MaybeUninit::zeroed(),
                values: MaybeUninit::uninit().assume_init(),
            }
        }
    }

    unsafe fn set_length(&mut self, length: usize) {
        assert!(length <= B);
        self.length = length;
    }

    fn new_root(
        pivot_key: K,
        pivot_value: V,
        left_node: Box<Node<K, V, B>>,
        right_node: Box<Node<K, V, B>>,
    ) -> Self {
        unsafe {
            let mut node = Node::new();
            node.keys[0].write(pivot_key);
            node.values[0].write(pivot_value);
            node.get_edge_uninit_mut(0).write(Some(left_node));
            node.get_edge_uninit_mut(1).write(Some(right_node));
            node.set_length(1);
            node
        }
    }

    unsafe fn get_edge(&self, index: usize) -> &Option<Box<Node<K, V, B>>> {
        if index >= B {
            self.right_edge.assume_init_ref()
        } else {
            self.edges[index].assume_init_ref()
        }
    }

    unsafe fn get_edge_mut(&mut self, index: usize) -> &mut Option<Box<Node<K, V, B>>> {
        self.get_edge_uninit_mut(index).assume_init_mut()
    }

    fn get_edge_uninit_mut(
        &mut self,
        index: usize,
    ) -> &mut MaybeUninit<Option<Box<Node<K, V, B>>>> {
        if index >= B {
            &mut self.right_edge
        } else {
            &mut self.edges[index]
        }
    }
}

enum InsertResult<K, V> {
    Inserted(Option<V>),
    Overflow(K, V),
}

impl<K, V, const B: usize> Node<K, V, B>
where
    K: Ord,
{
    fn left_of_index(&self, key: &K) -> (usize, bool) {
        unsafe {
            // Find index that the key is to the left of (or equal to)
            self.keys[0..self.length].iter().fold(
                (0, false),
                |(left_of_index, found), child_key| {
                    // SAFETY: up to self.length is guaranteed to be initialized
                    // This shouldn't require a branch, but it means comparing everything
                    match key.cmp(child_key.assume_init_ref()) {
                        Ordering::Less => (left_of_index, found),
                        Ordering::Equal => (left_of_index, true),
                        Ordering::Greater => (left_of_index + 1, found),
                    }
                },
            )
        }
    }

    fn search(&self, key: &K) -> Option<&V> {
        unsafe {
            let (left_of_index, found) = self.left_of_index(key);

            // If it was found, just return that value
            if found {
                debug_assert!(left_of_index < self.length);
                Some(self.values[left_of_index].assume_init_ref())
            } else {
                // Not found: search the node that it could be in
                self.get_edge(left_of_index).as_ref()?.search(key)
            }
        }
    }

    fn insert(&mut self, key: K, value: V) -> InsertResult<K, V> {
        unsafe {
            let length = self.length;
            let (left_of_index, found) = self.left_of_index(&key);

            // If it was found, just replace the value
            if found {
                debug_assert!(left_of_index < self.length);
                InsertResult::Inserted(Some(std::mem::replace(
                    self.values[left_of_index].assume_init_mut(),
                    value,
                )))
            } else if let Some(ref mut edge) = self.get_edge_mut(left_of_index) {
                // If not found, but there's an edge there, try to insert it into the edge
                match edge.insert(key, value) {
                    inserted @ InsertResult::Inserted(_) => inserted,
                    InsertResult::Overflow(key, value) => {
                        // An overflow was encountered while trying to insert. We need to split the
                        // edge @ left_of_index
                        if length < B {
                            let (split_key, split_value, right_node) = edge.split();
                            let is_right_of_split_key = key > split_key;
                            self.insert_at(left_of_index, split_key, split_value);
                            *self.get_edge_mut(left_of_index + 1) = Some(right_node);
                            // Try again
                            self.get_edge_mut(if is_right_of_split_key {
                                left_of_index + 1
                            } else {
                                left_of_index
                            })
                            .as_mut()
                            .expect("edge should not be None since it was set")
                            .insert(key, value)
                        } else {
                            // We can't split because we're full too. Send it upward
                            InsertResult::Overflow(key, value)
                        }
                    }
                }
            } else if self.length < B {
                // If not found, but we have space for it, shift it into place
                self.insert_at(left_of_index, key, value);
                InsertResult::Inserted(None)
            } else {
                // Not found, we are full. Get the caller to split and try again
                InsertResult::Overflow(key, value)
            }
        }
    }

    /// Shift everything toward the right to insert at the given position
    fn insert_at(&mut self, position: usize, key: K, value: V) {
        assert!(self.length < B);
        assert!(position < B);
        assert!(position <= self.length);

        unsafe {
            // Shift keys and values right
            std::ptr::copy(
                self.keys.as_ptr().offset(position as isize),
                self.keys.as_mut_ptr().offset(position as isize + 1),
                self.length - position,
            );
            std::ptr::copy(
                self.values.as_ptr().offset(position as isize),
                self.values.as_mut_ptr().offset(position as isize + 1),
                self.length - position,
            );
            self.keys[position].write(key);
            self.values[position].write(value);

            // Handle edges, which should be moved from position + 1
            if self.length + 1 == B {
                // Have to move the last edge into the right_edge
                self.right_edge.write(self.edges[B - 1].assume_init_read());
                std::ptr::copy(
                    self.edges.as_ptr().offset(position as isize + 1),
                    self.edges.as_mut_ptr().offset(position as isize + 2),
                    (self.length - position).saturating_sub(1),
                );
            } else {
                std::ptr::copy(
                    self.edges.as_ptr().offset(position as isize + 1),
                    self.edges.as_mut_ptr().offset(position as isize + 2),
                    self.length - position,
                );
            }
            self.get_edge_uninit_mut(position + 1).write(None);

            self.length += 1;
        }
    }

    /// Split the node in the middle
    fn split(&mut self) -> (K, V, Box<Node<K, V, B>>) {
        unsafe {
            // SAFETY: we can only do this operation if this is true. throw in a check for B for
            // good measure too
            assert!(self.length > 1 && self.length <= B);

            let middle = self.length / 2;
            // SAFETY: left_size and right_size will both be less than B
            let left_size = middle;
            let right_size = middle.saturating_sub(middle % 2);
            debug_assert_eq!(left_size + right_size + 1, self.length);

            // Create a manually dropped new node to put everything to the right of the middle into
            //
            //  1 2 3       -->              2
            // a b c d               1 x x       3 x x
            //                      a b x x     c d x x
            let mut new_node = ManuallyDrop::new(Box::new(Node::new()));
            std::ptr::copy_nonoverlapping(
                self.keys.as_ptr().offset(middle as isize + 1),
                new_node.keys.as_mut_ptr(),
                right_size,
            );
            std::ptr::copy_nonoverlapping(
                self.values.as_ptr().offset(middle as isize + 1),
                new_node.values.as_mut_ptr(),
                right_size,
            );
            std::ptr::copy_nonoverlapping(
                self.edges.as_ptr().offset(middle as isize + 1),
                new_node.edges.as_mut_ptr(),
                right_size + 1,
            );
            if self.length == B {
                // Move the right edge into the end of the edges
                new_node.edges[right_size].write(self.right_edge.assume_init_read());
            }
            // End of moves, can set the lengths appropriately
            self.set_length(left_size);
            new_node.set_length(right_size);
            // SAFETY: now that we've set the lengths, it's safe to take middle, because it won't be
            // dropped twice if something goes wrong.
            let split_key = self.keys[middle].assume_init_read();
            let split_value = self.values[middle].assume_init_read();
            (split_key, split_value, ManuallyDrop::into_inner(new_node))
        }
    }
}

impl<K, V, const B: usize> Drop for Node<K, V, B> {
    fn drop(&mut self) {
        unsafe {
            // SAFETY: valid up to self.length
            for key in &mut self.keys[0..self.length] {
                key.assume_init_drop();
            }
            // SAFETY: valid up to self.length + 1
            for edge in self.edges.iter_mut().take(self.length + 1) {
                edge.assume_init_drop();
            }
            // SAFETY: valid if self.length == B
            if self.length == B {
                self.right_edge.assume_init_drop();
            }
            // SAFETY: valid up to self.length
            for value in &mut self.values[0..self.length] {
                value.assume_init_drop();
            }
            self.set_length(0);
        }
    }
}

#[test]
fn test_insert_get() {
    let mut tree = Optimap::<u32, u32, 6>::new();

    for n in 0..100 {
        tree.insert(n, n * 2);
    }

    println!("{tree:#?}");

    assert_eq!(tree.get(&50), Some(&100));
}
