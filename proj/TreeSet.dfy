// Function type for comparing elements
// TODO: depois ver se consigo por tipo generico mesmo
type T = int // for demo purposes, but could be real, etc.

// **********************************************************************
// Represents a binary search tree node, for elements of type T.

class BTNode {
  var value: T; // value of the node
  var left: BTNode?;  // left child of the node (? - may be null)
  var right: BTNode?; // right child of the node (? - may be null)

  // Constructor of the class.
  constructor (value: T, left: BTNode?, right: BTNode?) 
    ensures this.value == value
    ensures this.left == left
    ensures this.right == right
  {
    this.value := value;
    this.left := left;
    this.right := right;
  }
}

// **********************************************************************
// Represents a sorted set of elements of type T.

// TODO: depois, ver se devia fazer com que bst fosse balanced (prob nao)
// TODO: como ter a certeza que não há duplicados?
class {:autocontracts} TreeSet {
  // Ghost variable used for specification & verification purposes.
  // Holds the set of values in the subtree starting in this node (inclusive). 
  ghost var elems : set<T>;
  
  // Concrete state variable with internal representation (initially filled with Nil). 
  var root: BTNode?;

  // Predicate that formalizes the class invariant. Makes sure that the binary tree starting at
  // root is sorted (it is a binary search tree), and connects the abstract state variable (elems)
  // to the actual set of elements in the binary tree, using the BTtoSet() function.
  predicate Valid()
  {
    isBST(root) &&
    elems == BSTtoSet(root)
  }

  // Predicate that indicates if the binary tree is correctly sorted, and is a valid BST.
  predicate isBST(node : BTNode?)
    reads node
    decreases root, elems
  {
    if node == null
    then true
    else (node.left != null ==> forall k :: k in BSTtoSet(node.left) ==> k < node.value) && 
         (node.right != null ==> forall k :: k in BSTtoSet(node.right) ==> k > node.value) &&
         isBST(node.left) && isBST(node.right)
  }

  function BSTtoSet(node : BTNode?) : set<T>
    decreases node
  {
    if node == null
    then {}
    else {node.value} + BSTtoSet(node.left) + BSTtoSet(node.right)
  }

  // Receives the hash function to be used and initializes the set as empty.
  constructor ()
    ensures this.elems == {}
  {
    this.root := null;
    this.elems := {};
  }

  // Inserts a new element x into the sorted set (binary search tree).
  method insert(x : T) 
    requires x !in elems
    ensures elems == old(elems) + {x}
  {
    root := this.insertAux(x, root);
    this.elems := this.elems + {x};
  }

  method insertAux(x : T, node : BTNode?) returns (res : BTNode?)
  {
    // TODO: insert method
  }

  // Deletes an element X from the sorted set (binary search tree).
  method delete(x : T) 
    requires x in elems
    ensures elems == old(elems) - {x}
  {
    root := this.deleteAux(x, root);
    elems := elems - {x};
  }

  method deleteAux(x : T, node : BTNode?) returns (res : BTNode?)
  {
    // TODO: delete method
  }

  // Check if the subtree starting in this node contains a value 'x'.
  method contains(x: T) returns (res: bool)
    ensures res <==> x in elems
  {
    res := this.containsAux(x, root);
  }

  method containsAux(x: T, node: BTNode?) returns (res: bool)
    ensures res <==> x in BSTtoSet(node)
  {
    // TODO: contains method
  }

  // Returns an ordered sequence with all the elements of the BST.
  // Need to do an inorder traversal of the tree (left subtree first, then root, then right subtree).
  method asSeq() returns (res : seq<T>)
    ensures multiset(res) == multiset(elems)
    ensures forall k1, k2 :: 0 <= k1 < k2 < |res| ==> res[k1] < res[k2]
    decreases elems
  {
    // TODO: talvez seja preciso lemma para provar que subtree da esquerda é menor e a da direita é maior?
    // TODO: asSeq method
  }
}

// -------------------------------------------

// A simple test case, checked statically by Dafny.
method testHashSet() {
  // TODO: fazer test case com as várias operações que a classe permite
}