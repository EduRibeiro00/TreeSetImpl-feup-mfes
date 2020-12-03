// A datatype that stores a value of type T or Nil (no value) 
datatype Option<T> = Nil | Some(value: T)

// Represents a sorted set of elements of type T. 
class {:autocontracts} SortedSet<T(==)> {

  // Abstract state variable used for specification purposes only (set of elements in the sorted set).  
  ghost var elems : set<T>;

  // Concrete state variable with internal representation (initially filled with Nil). 
  // TODO: ver representacao de uma BST

  // Internal parameter, with initial size of sorted set.
  const initialCapacity := 101;



  // Predicate that formalizes the class invariant.
  predicate Valid() { 
    true
    // TODO: class invariant
  }

  // Receives the hash function to be used and initializes the set as empty.
  constructor () {

  }

  // Inserts a new element x into the sorted set (binary search tree).
  method insert(x : T) {

  }

  // Deletes an element X from the sorted set (binary search tree).
  method delete(x : T) {

  }


  // Checks if an element X is in the sorted set (binary search tree).
  method contains(x: T) returns (res: bool)
  {
    return false;
  }
}

// -------------------------------------------

// A simple test case, checked statically by Dafny.
method testHashSet() {
  // TODO: fazer test case com as várias operações que a classe permite
}