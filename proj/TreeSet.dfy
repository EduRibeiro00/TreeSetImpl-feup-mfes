type T = int // for demo purposes, but could be real, etc.

// TODO: ver melhor as clauses/ensures e isso com o Repr

// helper function to check if a value is the smallest element in a set
predicate isMin(x: T, arr: set<T>)
{
  forall elem :: elem in arr ==> x <= elem
}

// helper function to check if a sequence is in strictly increasing order
predicate isSorted(arr: seq<T>)
{
  forall k1, k2 :: 0 <= k1 < k2 < |arr| ==> arr[k1] < arr[k2]
}

// **********************************************************************
// Represents a binary search tree node, for elements of type T.
class {:autocontracts} BSTNode {
  // ghost variable representing a set of all the elems that are in the BST which root is this node
  ghost var elems: set<T>;

  // ghost variable representing a set of all the node objects that are in the BST which root is this node
  ghost var Repr: set<object>;

  // value of the node
  var value: T;

  // left child of the node (? - may be null)
  var left: BSTNode?;

  // right child of the node (? - may be null)
  var right: BSTNode?;

  // class invariant of the BSTNode class
  predicate Valid()
  {
    // check if this node is in Repr
    this in Repr &&

    // check correctness for left subtree:
    // check if Repr contains left and all nodes of the left subtree
    // check if left's Repr does not contain the current node, to avoid cycles
    // check class invariant for left node
    // check if all nodes on left subtree are less than the current node
    (left != null ==> 
      left in Repr &&
      left.Repr <= Repr && this !in left.Repr &&
      left.Valid() &&
      (forall elem :: elem in left.elems ==> elem < value)) &&

    // check correctness for right subtree:
    // check if Repr contains right and all nodes of the right subtree
    // check if right's Repr does not contain the current node, to avoid cycles
    // check class invariant for right node
    // check if all nodes on right subtree are higher than the current node
    (right != null ==> 
      right in Repr &&
      right.Repr <= Repr && this !in right.Repr &&
      right.Valid() &&
      (forall elem :: elem in right.elems ==> value < elem)) &&

    // case where the node does not have any subtrees:
    // connect ghost variable elems with its intended value
    (left == null && right == null ==>
      elems == {value}) &&

    // case where only left subtree exists:
    // connect ghost variable elems with its intended value
    (left != null && right == null ==>
      elems == left.elems + {value}) &&

    // case where only right subtree exists:
    // connect ghost variable elems with its intended value
    (left == null && right != null ==>
      elems == {value} + right.elems) &&

    // case where both left and right subtrees exist:
    // check if left and right subtrees are disjoint (i.e. no node belongs to both)
    // connect ghost variable elems with its intended value
    (left != null && right != null ==>
      left.Repr !! right.Repr &&
      elems == left.elems + {value} + right.elems)
  }

  // constructor of the class. Creates a single node with no children
  constructor (data: T) 
    ensures elems == {data}
    ensures Repr == {this}
  {
    value := data;
    left := null;
    right := null;
    elems := {data};
    Repr := {this};
  }

  // method that checks if a given value is present in the BST
  function method contains(x: T) : bool
    ensures contains(x) <==> x in elems
  {
    // if value is equal to the root, return true
    if x == value then true
    
    // if the value is smaller, check on left subtree 
    else if left != null && x < value then left.contains(x)

    // if the value is higher, check on right subtree
    else if right != null && x > value then right.contains(x)

    // value is not present in the BST
    else false
  }

  // method that deletes a value from the BST
  // returns the new root of the tree (null if the last node of the BST has been deleted)
  method delete(x: T) returns (node: BSTNode?)
    decreases Repr
    ensures fresh(Repr - old(Repr))
    ensures node == null ==> old(elems) <= {x}
    ensures node != null ==> node.Valid() && node.Repr <= Repr && node.elems == old(elems) - {x}
  {
    node := this;
    // if the 'x' value is less than the current value, try deleting in left subtree
    if left != null && x < value {
      // left.delete() will return the left subtree's new root
      var t := left.delete(x);
      // update left subtree's root
      left := t;
      // remove element from ghost variable
      elems := elems - {x};
      // update Repr variable
      if left != null { Repr := Repr + left.Repr; }
    }

    // if the 'x' value is higher tahn the current value, try deleting in right subtree
    else if right != null && value < x {
      // right.delete() will return the right subtree's new root
      var t := right.delete(x);
      // update right subtree's root
      right := t;
      // remove element from ghost variable
      elems := elems - {x};
      // update Repr variable
      if right != null { Repr := Repr + right.Repr; }
    }

    // if the element that we want to delete is the current node (root),
    // then we need to get a new root for the tree
    else if x == value {
      // if this node is the last one in the tree, there are no nodes left
      if left == null && right == null {
        node := null;
      }
      // if there is no left subtree, new root is the root of the right subtree
      else if left == null {
        node := right;
      }
      // if there is no right subtree, new root is the root of the left subtree
      else if right == null {
        node := left;
      }
      // if both subtrees exist, new root is the inorder successor of the node
      else {
        // find in order successor of the node: the leftmost (smaller) element
        // in the right subtree
        var min_val, new_r := right.deleteMin();
        // update node's value
        value := min_val;
        // update node's right subtree root
        right := new_r;
        // update ghost variable
        elems := elems - {x};
        // update Repr variable
        if right != null { Repr := Repr + right.Repr; }
      }
    }
  }


  // method that removes and returns the smaller element of a BST
  // used by the delete() method when it needs to find the inorder successor
  // of the root (i.e. the smaller element in the right subtree)
  // returns the value of the smallest element, and the new root of the tree
  method deleteMin() returns (min: T, node: BSTNode?)
    decreases Repr
    ensures fresh(Repr - old(Repr))
    ensures node == null ==> old(elems) == {min}
    ensures node != null ==> node.Valid() && node.Repr <= Repr && node.elems == old(elems) - {min}
    ensures min in old(elems) && isMin(min, old(elems))
  {
    // the minimum element is the leftmost element in the left subtree
    // if the current node does not have a left child, then it is the min value
    if left == null {
      // update values to return
      min := value;
      node := right;
    }
    // node has left child; it is not the minimum. Keep iterating through left subtree
    else {
      var new_lr;
      // delete the minimum in left subtree
      min, new_lr := left.deleteMin();
      // update new left subtree root
      left := new_lr;
      // root of the tree starting at this node is still this node
      node := this;
      // update ghost variables
      elems := elems - {min};
      if left != null { Repr := Repr + left.Repr; }
    }
  }

  // method that returns an ordered sequence of all the elements of the BST
  method asSeq() returns (res: seq<T>)
    decreases Repr
    ensures multiset(res) == multiset(elems)
    ensures isSorted(res)
  {
    var left_seq : seq<T> := [];
    var right_seq : seq<T> := [];
    if left != null {
      left_seq := left.asSeq();
    }
    if right != null {
      right_seq := right.asSeq();
    }

    res := left_seq + [value] + right_seq;
  }
}

// **********************************************************************
// Represents a sorted set of elements of type T. Implemented with a binary search tree
class {:autocontracts} TreeSet {
  // ghost variable representing a set of all the elems that are in the set
  ghost var elems: set<T>;

  // TODO: ver melhor o que é que este Repr quer dizer
  // ghost variable representing a set of all the node objects that are in the set
  ghost var Repr: set<object>;

  // variable that represents the root of the BST that implements this sorted set
  var root: BSTNode?

  // class invariant of the TreeSet class
  predicate Valid()
  {
    this in Repr &&
    // if the root is null, then the set must be empty
    (root == null ==> elems == {}) &&
    // if the root exists...
    (root != null ==> 
      root in Repr && root.Repr <= Repr && this !in root.Repr &&
      // check root's class invariant and connect ghost variable with its intended value
      root.Valid() &&
      elems == root.elems)
  }

  // constructor of the class. Creates an empty set
  constructor()
    ensures fresh(Repr - {this})
    ensures elems == {}
  {
    root := null;
    Repr := {this};
    elems := {};
  }

  // method that checks if a given value is present in the set
  // checks if it is present in the binary search tree
  function method contains(x: T) : bool
    ensures contains(x) <==> x in elems
  {
    root != null && root.contains(x)
  }

  // method that inserts a new value into the set
  // creates a new node and inserts it in the BST
  method insert(x: T)
    requires x !in elems
    ensures fresh(Repr - old(Repr))
    ensures elems == old(elems) + {x}
  {
    // insert value using helper method; returns new root of BST
    var new_root := insertAux(x, root);
    // update BST root
    root := new_root;
    // update ghost variables
    elems := root.elems;
    Repr := root.Repr + {this};
  }

  // helper method for inserting a new value in the sorted set 
  static method insertAux(x: T, n: BSTNode?) returns (new_root: BSTNode)
    requires n == null || n.Valid()
    modifies if n != null then n.Repr else {}
    ensures new_root.Valid()
    ensures n == null ==> fresh(new_root) && fresh(new_root.Repr) && new_root.elems == {x}
    ensures n != null ==> n == new_root && fresh(n.Repr - old(n.Repr)) && n.elems == old(n.elems) + {x}
    decreases if n == null then {} else n.Repr
  {
    // if the old root is empty, i.e. the set is empty
    if n == null {
      // just need to create a new node, that is the new root
      new_root := new BSTNode(x);
    }
    // new value is equal to the current node's value; don't change anything
    else if x == n.value {
      new_root := n;
    }
    else {
      // new value is less than current node's value; should be inserted in the left subtree
      if x < n.value {
        // insert in left subtree, get new root of left subtree
        var new_lr := insertAux(x, n.left);
        // update new root and ghost variable
        n.left := new_lr;
        n.Repr := n.Repr + n.left.Repr;
      }
      // new value is higher than current node's value; should be inserted in the right subtree
      else {
        // insert in right subtree, get new root of right subtree
        var new_rr := insertAux(x, n.right);
        // update new root and ghost variable
        n.right := new_rr;
        n.Repr := n.Repr + n.right.Repr;
      }

      // BST root already existed, so root didn't change 
      new_root := n;
      // add newly added element to the root's elems 
      n.elems := n.elems + {x};
    }
  }

  // method that deletes a value from the sorted set
  method delete(x: T)
    requires x in elems
    ensures fresh(Repr - old(Repr))
    ensures elems == old(elems) - {x}
  {
    if root != null {
      // call delete() method from BST root, to delete the value and get new root
      var new_root := root.delete(x);
      // update BST root
      root := new_root;
      // if the new root exists, update ghost variables accordingly
      if root != null {
        elems := root.elems;
        Repr := root.Repr + {this};
      }
      // root is null; set/BST is now empty. Reset the ghost variables
      else {
        elems := {};
        Repr := {this};
      }
    }
  }

  // method that returns an ordered sequence of all the elements in the set
  method asSeq() returns (res: seq<T>)
    ensures multiset(res) == multiset(elems)
    ensures isSorted(res)
  { 
    // if the set is not empty, return BST sequence from root
    if root != null {
      res := root.asSeq();
    }
    // is set is empty, return empty sequence
    else {
      res := [];
    }
  }
  
  // simple method that checks if the set is empty or not
  predicate method isEmpty()
    ensures isEmpty() <==> (|elems| == 0)
  {
    root == null
  }
}

// **********************************************************************
// A test case, checked statically by Dafny, that covers the 
// insert(), delete() and contains() methods of the TreeSet class
method testTreeSetInsertionDeletion()
{
  // create new set
  var s := new TreeSet();
  // check that set is empty
  assert s.isEmpty();

  // insert two elements
  s.insert(2);
  s.insert(9);
  // check if the set is not empty anymore
  assert !s.isEmpty();
  // check that, for any contains() call that we do on the TreeSet,
  // it will only be true if the argument of the call is either 2 or 9,
  // because they are the only elements on the set
  var x;
  var isPresentInSet := s.contains(x);
  assert isPresentInSet <==> x == 2 || x == 9;

  // delete element
  s.delete(9);
  
  // add new element
  s.insert(4);

  // check that the set is not empty; still some elements left
  assert !s.isEmpty();
  var y;
  var isPresentInSet2 := s.contains(y);
  assert isPresentInSet2 <==> y == 2 || y == 4;

  // delete rest of the elements
  s.delete(2);
  s.delete(4);

  // check that the elements that were deleted are no longer in the set
  assert !s.contains(2);
  assert !s.contains(4);
  assert !s.contains(9);

  // check that set is empty again
  assert s.isEmpty();
}

// A test case, checked statically by Dafny, that covers the 
// isSeq() method of the TreeSet class
method testTreeSetSequence()
{
  // create new set
  var s := new TreeSet();
  
  // check that the sequence that the asSeq() method returns is empty
  var sequence := s.asSeq();
  assert sequence == [];

  // insert a bunch of elements
  s.insert(2);
  s.insert(3);
  s.insert(5);
  s.insert(4);
  s.insert(10);
  s.insert(1);
  s.insert(8);

  // check that the returned sequence has the same elements and is sorted
  // sequence := s.asSeq();
  // assert sequence == [1, 2, 3, 4, 5, 8, 10];

  // delete some of the elements
  s.delete(1);
  s.delete(10);
  s.delete(3);
  s.delete(5);

  // check the sequence of elements
  // sequence := s.asSeq();
  // assert sequence == [2, 4, 8];

  // delete the rest of the elements
  s.delete(2);
  s.delete(4);
  s.delete(8);

  // check that the set is now completely empty
  assert s.isEmpty();
  // check that the sequence that the asSeq() method returns is now empty
  // sequence := s.asSeq();
  // assert sequence == [];
}

// A test case, checked statically by Dafny, that should fail
// because of incorrect call to the TreeSet delete() method
method testTreeSetFailDelete()
{
  // create new set
  var s := new TreeSet();

  // insert some elements
  s.insert(2);
  s.insert(4);
  s.insert(6);

  // this method call fails the static analysis done by Dafny, because
  // a precondition for this method is not verified: the number 7 is not
  // on the set, so it cannot be deleted
  s.delete(7);
}

// A test case, checked statically by Dafny, that should fail
// because of incorrect call to the TreeSet insert() method
method testTreeSetFailInsert()
{
  // create new set
  var s := new TreeSet();

  // insert some elements
  s.insert(2);
  s.insert(4);
  s.insert(6);

  // this one should also fail the static analysis, once again because it
  // does not satisfy the precondition that an element that is already
  // on the set cannot be inserted again
  s.insert(2);
}