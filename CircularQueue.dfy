class {:autocontracts} CircularQueue {

    // Atributos
    var queue: array<int>;
    var tail: nat;
    var header: nat;
    

    // Abstração
    ghost var Content: seq<int>;

    ghost predicate Valid()
    {
        0 <= header < queue.Length &&
        0 <= tail < queue.Length &&
        header < tail  ==> Content == queue[header..tail+1] &&
        header > tail  ==> Content == queue[..tail+1] + queue[header..] &&
        |Content| == 0 ==> Content == []
    }

    constructor()
        ensures Content == []
    {
        queue := new int[1];
        header := 0;
        tail := 0;
        Content := [];
    }

    method insert(item:int)    
        ensures Content == old(Content) + [item]
        ensures |Content| == old(|Content|) + 1
    {
        Content := Content + [item];

        if queue.Length != 0{

            if ((tail + 1) % queue.Length) == header {
                if header < tail{
                    var newQueue : array := new int[queue.Length + 5];
                    forall i | 0 <= i < queue.Length
                    {
                        newQueue[i] := queue[i];
                    }

                    newQueue[queue.Length] := item;
                    queue:= newQueue;
                    tail := (tail + 1) % queue.Length;
                }
                else{
                    var newQueue : array := new int[queue.Length + 5];

                    forall i | 0 <= i < tail + 1
                    {
                        newQueue[i] := queue[i];
                    }

                    newQueue[tail + 1] := item;

                    forall i | tail + 1 <= i < queue.Length
                    {
                        newQueue[i+5] := queue[i];
                    }

                    // [5,4,1,2,3]
                    // [5,4,8,x,x,x,x,1,2,3]

                    queue:= newQueue;
                    tail := (tail + 1) % queue.Length;
                    header := (header + 5) % queue.Length;
                }

            }else{
                queue[(tail + 1) % queue.Length] := item;
            }
        }
    }

    method contains(item: int) returns (contains: bool)
        ensures contains == true ==> item in Content
        ensures contains == false ==> item !in Content
        {
            var i: nat := 0;
            contains := false;

            while (i < queue.Length)
            decreases queue.Length - i
            invariant 0 <= i <= queue.Length
            invariant !contains ==> forall j :: 0 <= j < i ==> queue[j] != item
            {
            if (queue[i] == item) {
                contains := true;
                break;
            }
            i := i + 1;
            }
        }

    method remove() returns (item:int)
        requires |Content| > 0
        ensures item == old(Content)[0]
        ensures Content == old(Content)[1..]
        //achar algum jeito de dizer qual o header

    function size():nat
    ensures size() == |Content|

    function isEmpty():bool
    ensures isEmpty() == (|Content| == 0)

    
    

    method mergeQueues(otherQueue: CircularQueue) returns (mergedQueue: CircularQueue) 
    
}
method Main() {
    var queue := new CircularQueue();
    assert queue.Content == [];
    assert queue.Content != [1];
    queue.insert(3);

    assert queue.Content == [3];
    assert queue.Content != [2];
    
    queue.insert(6);

    assert queue.Content == [3,6];
    assert queue.Content != [3,2];



}