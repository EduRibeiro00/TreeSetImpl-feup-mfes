// A datatype that stores a value of type T or Nil (no value) 
datatype Option<T> = Nil | Some(value: T)

// Function type for comparing elements
type ComparatorFunction<!T> = (T) -> nat 

// Represents a sorted set of elements of type T. 
class {:autocontracts} TreeSet<T(==)> {

  // Abstract state variable used for specification purposes only (set of elements in the sorted set).  
  ghost var elems : set<T>;

   // Comparator function that it is passed to the tree set, so it can order its elements. 
  const comp_func: ComparatorFunction<T>;

  const initializer: nat -> T; // required by new T[]

  // Concrete state variable with internal representation (initially filled with Nil). 
  // TODO: ver representacao de uma BST


  // Predicate that formalizes the class invariant.
  predicate Valid() { 
    true
    // TODO: class invariant
  }

  // Receives the hash function to be used and initializes the set as empty.
  constructor (comp_func: ComparatorFunction<T>) 
    ensures elems == {}
    ensures this.comp_func == comp_func
  {
    this.comp_func := comp_func;
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

  }

  // Returns an ordered sequence with all the elements of the sorted set (binary search tree).
  method asSeq() returns (res: seq<T>)
  {

  }
}

// -------------------------------------------

// A simple test case, checked statically by Dafny.
method testHashSet() {
  // TODO: fazer test case com as várias operações que a classe permite
}