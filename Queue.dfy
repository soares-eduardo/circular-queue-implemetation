class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var queueSize: nat;
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    queueSize == circularQueue.Length &&
    Content == circularQueue[0..circularQueue.Length]
  }

  // Construtor
  constructor()
    ensures circularQueue.Length == 0
    ensures front == 0 && rear == 0
    ensures Content == [] // REVISAR
    ensures counter == 0
  {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    queueSize := 0;
    Content := [];
    counter := 0;
  }

  // Métodos

  // 1 - 
  method insert(item: int)
    // ensures Content == old(Content) + [item];
    

  method remove(item: int)
    requires |Content| > 0
    ensures item == old(Content)[0]
    ensures Content == old(Content)[1..]

  method size() returns (size:nat)
    ensures size == counter
  {
    size := counter;
  }

  method isEmpty() returns (isEmpty: bool)
    ensures isEmpty == (counter == 0);
  {
    isEmpty := if counter == 0 then true else false;
  }

  method contains(item: int) returns (contains: bool)
    ensures contains == true ==> item in circularQueue[..]
    ensures contains == false ==> item !in circularQueue[..]
    ensures Content == old(Content)
  {
    var i: nat := 0;
    contains := false;

    while (i < circularQueue.Length)
      decreases circularQueue.Length - i
      invariant 0 <= i <= circularQueue.Length
      invariant !contains ==> forall j :: 0 <= j < i ==> circularQueue[j] != item
    {
      if (circularQueue[i] == item) {
        contains := true;
        break;
      }
      i := i + 1;
    }
  }

  // TODO
  // method mergeQueues() returns (mergedQueue:array<int>)
}

method Main ()
{
  var circularQueue := new Queue();
  assert circularQueue.circularQueue.Length == 0;
  assert circularQueue.Content == [];
  assert circularQueue.Content != [1];

  var isQueueEmpty := circularQueue.isEmpty();
  assert isQueueEmpty == true;

  var queueSize := circularQueue.size();
  assert queueSize == 0;

}