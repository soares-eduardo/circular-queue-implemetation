class {:autocontracts} Queue {

  // Atributos
  var circularQueue: array<int>;
  var rear: nat;  // cauda
  var front: nat; // head
  var counter: nat;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
  {
    0 <= counter <= circularQueue.Length &&
    0 <= front &&
    0 <= rear &&
    Content == circularQueue[..]
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
    Content := [];
    counter := 0;
  }

  method insert(item: int)
    // requires rear <= circularQueue.Length
    // ensures (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == [item] &&
    //       |Content| == 1
    //     )
    // ensures circularQueue.Length != 0 ==>
    // (
    //   (front == 0 && rear == 0 && circularQueue.Length == 1) ==>
    //     (
    //       Content == old(Content)  &&
    //       |Content| == old(|Content|)

    //     )
    // ||
    //   (front == 0 && rear == circularQueue.Length-1 ) ==> 
    //     (
    //       Content == old(Content) + [item] &&
    //       |Content| == old(|Content|) + 1
    //     )
    // ||
    //   (rear + 1 != front && rear != circularQueue.Length-1 && rear + 1 < circularQueue.Length - 1) ==> 
    //     (
    //       Content == old(Content[0..rear]) + [item] + old(Content[rear..circularQueue.Length])
    //     )
    // ||
    //   (rear + 1 == front) ==> 
    //   (
    //     Content[0..rear + 1] == old(Content[0..rear]) + [item] &&
    //     forall i :: rear + 2 <= i <= circularQueue.Length ==> Content[i] == old(Content[i-1])
    //   )
    // )
    {

      //counter := counter + 1;
      // if front == 0 && rear == 0 && circularQueue.Length == 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   queueInsert[0] := item;
      //   circularQueue := queueInsert;
      //   Content := [item];
      //   rear := rear + 1;
      // }   
      // else if front == 0 && rear == circularQueue.Length-1 && circularQueue.Length > 0
      // {
      //   var queueInsert: array<int>;
      //   queueInsert := new int [circularQueue.Length + 1];
      //   var i: nat := 0;
      //   while i < circularQueue.Length
      //   invariant circularQueue.Length + 1 == queueInsert.Length
      //   {
      //     queueInsert[i] := circularQueue[i];
      //     i := i + 1;
      //   }
      //   queueInsert[queueInsert.Length - 1] := item;
      //   Content := Content + [item];
      //   rear := rear + 1;
      //   circularQueue := queueInsert;
      // }
    }

  method auxInsertEmptyQueue(item:int)
    requires front == 0 && rear == 0 && circularQueue.Length == 0
    ensures circularQueue.Length == 1
    ensures Content == [item]
    ensures |Content| == 1
    ensures rear == 1
    ensures counter == old(counter) + 1
    ensures front == 0
  {
    counter := counter + 1;
    var queueInsert: array<int>;
    queueInsert := new int [circularQueue.Length + 1];
    queueInsert[0] := item;
    circularQueue := queueInsert;
    Content := [item];
    rear := rear + 1;
  }

  method auxInsertEndQueue(item:int)
    requires front == 0 && rear == circularQueue.Length && circularQueue.Length >= 1
    ensures Content == old(Content) + [item]
    ensures |Content| == old(|Content|) + 1
    ensures front == 0
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
  // {
  //   counter := counter + 1;
  //   var queueInsert: array<int>;
  //   queueInsert := new int [circularQueue.Length + 1];
  //   var i: nat := 0;
  //   while i < circularQueue.Length
  //   invariant circularQueue.Length + 1 == queueInsert.Length
  //   invariant 0 <= i <= circularQueue.Length
  //   invariant forall j :: 0 <= j < i ==> queueInsert[j] == circularQueue[j]
  //   {
  //     queueInsert[i] := circularQueue[i];
  //     i := i + 1;
  //   }
  //   queueInsert[queueInsert.Length - 1] := item;
  //   Content := Content + [item];
  //   rear := rear + 1;
  //   circularQueue := queueInsert;
  // }

  method auxInsertSpaceQueue(item:int)
    requires rear < front && front < circularQueue.Length
    ensures rear == old(rear) + 1
    ensures counter == old(counter) + 1
    ensures Content == old(Content[0..rear]) + [item] + old(Content[rear+1..circularQueue.Length])
    ensures |Content| == old(|Content|) + 1

  method auxInsertInitQueue(item:int)

  method auxInsertBetweenQueue(item:int)

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

  circularQueue.auxInsertEmptyQueue(2);
  assert circularQueue.Content == [2];
  assert circularQueue.counter == 1;
  assert circularQueue.circularQueue.Length == 1;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 1;
  assert circularQueue.rear != 2;
  assert circularQueue.front != 2;

  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2,4];
  assert circularQueue.counter == 2;
  assert circularQueue.front == 0;
  assert circularQueue.rear == 2;

  circularQueue.auxInsertEndQueue(4);
  assert circularQueue.Content == [2,4,4];
  assert circularQueue.counter == 3;

  circularQueue.auxInsertEndQueue(56);
  assert circularQueue.Content == [2,4,4,56];
  assert circularQueue.counter == 4;

}