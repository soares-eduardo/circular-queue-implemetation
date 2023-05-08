class {:autocontracts} Queue {
      // Atributos
  var circularQueue: array<int>;
  var rear: int;
  var front: int;

  // Abstração
  ghost var Content: seq<int>;

  // Predicado
  ghost predicate Valid()
    {
    
    }

    // Construtor
    constructor()
      ensures Content == []
    {
    circularQueue := new int[0];
    rear := 0;
    front := 0;
    Content := [];
    }

  // Métodos

  method insert(item: int)
    ensures Content == old(Content) + [item]

  method remove(item: int)
    requires |Content| > 0
    ensures item == old(Content)[0]
    ensures Content == old(Content)[1..]

  method size() returns (size:nat)
    ensures size == |Content|
    ensures Content == old(Content)

  // TODO
  // method contains()
  // method isEmpty() returns (isEmpty:bool)
  // method mergeQueues() returns (mergedQueue:array<int>)
}