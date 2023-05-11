class {:autocontracts} CircularQueue {

    // Atributos
    var queue: array<int>;
    var tail: nat;
    var header: nat;
    

    // Abstração
    ghost var Content: seq<int>;
    ghost var Counter: nat;

    // Predicado
    ghost predicate Valid()
    {
        0 <= Counter <= queue.Length &&
        0 <= header <= queue.Length &&
        0 <= tail <= queue.Length &&
        header < tail && Counter > 0 ==> Content == queue[header..tail] &&
        header > tail && Counter > 0 ==> Content == queue[..tail] + queue[header..] &&
        Counter == 0 ==> Content == [] &&
        Counter == |Content| &&
        |Content| <= queue.Length
    }

    constructor()
        ensures Content == []
        ensures Counter == 0
        ensures header == 0
        ensures tail == 0
    {
        queue := new int[0];
        header := 0;
        tail := 0;
        Content := [];
        Counter := 0;
    }

    method insert(item:int)      
        ensures Content == old(Content) + [item]
        ensures Counter == old(Counter) + 1
        //achar algum jeito de dizer qual o tail

    method remove() returns (item:int)
        requires |Content| > 0
        ensures item == old(Content)[0]
        ensures Content == old(Content)[1..]
        ensures Counter == old(Counter) - 1
        //achar algum jeito de dizer qual o header

    function size():nat
    ensures size() == |Content|

    function isEmpty():bool
    ensures isEmpty() == (|Content| == 0)

    function contains(item: int):bool
    ensures contains(item) == (item in Content)

    method mergeQueues(otherQueue: CircularQueue) returns (mergedQueue: CircularQueue) 
    
}
method Main() {
    var queue := new CircularQueue();

    assert queue.Content == [];
    assert queue.Content != [1];
    assert queue.header == 0;
    assert queue.header != 1;

    queue.insert(3);

    assert queue.Content == [3];
    assert 3 in queue.Content;
    assert queue.Content != [5];
    assert queue.Content != [3,3];

    assert queue.contains(3);
    assert !queue.contains(10);
    assert queue.header == 0;
    assert queue.header != 1;
    assert queue.tail == 1;
    assert queue.tail != 3;
 
    queue.insert(6);

    assert queue.Content == [3,6]; 
    assert queue.Content != [5];
    assert queue.Content != [3,6,4];
    assert queue.header == 0;
    assert queue.header != 1;
    assert queue.tail == 2;
    assert queue.tail != 3;


}