/*
Integrantes:
- Eduardo Cardoso
- Eduardo Soares
- Jéssica Freua
- Kevin Boucinha
- Tobias Trein

Objetivo: Implementação de uma fila circular (FIFO).
*/

class {:autocontracts} CircularQueue
{
    // concrete
    var front: nat;
    var count: nat; 
    var queue: array<int>;

    // abstract
    ghost var ghostQueue: seq<int>;
    
    ghost predicate Valid() 
    { 
        queue.Length > 0
        && count == |ghostQueue|
        && 0 <= count <= queue.Length
        && 0 <= front < queue.Length
        && if front + count <= queue.Length
        then ghostQueue == queue[front..front + count]
        else ghostQueue == queue[front..] + queue[..front + count - queue.Length]
    }

    constructor (size:nat := 5)
        requires size > 0
        ensures queue.Length == size
        ensures ghostQueue == []
    {
        queue := new int[size];
        front := 0;
        count := 0;
        ghostQueue := [];
    }

    method enqueue(obj: int)
        ensures ghostQueue == old(ghostQueue) + [obj]
        ensures |ghostQueue| == old(|ghostQueue|) + 1
    {

        if count == queue.Length 
        { 
            var double := queue.Length;
            var newQueue := new int[queue.Length + double];
            
            
            forall i| 0 <= i < queue.Length 
            {
                newQueue[if i < front then i else i + double] := queue[i];
            }
            
            queue := newQueue;
            front := front + double;
        }

        var rear := front + count;
        if rear < queue.Length 
        {
            queue[rear] := obj;
        } else 
        {
            queue[rear - queue.Length] := obj;
        }

        count := count + 1;
        ghostQueue := ghostQueue + [obj];
    }

    method dequeue() returns (obj: int)
        requires ghostQueue != []
        ensures obj == old(ghostQueue)[0]
        ensures ghostQueue == old(ghostQueue)[1..]
    {
        obj := queue[front];
        front := if front == queue.Length - 1 then 0 else front + 1;
        count := count - 1;
        ghostQueue := ghostQueue[1..];
    }

    method has(obj: int) returns (contains: bool)
        ensures contains <==> obj in ghostQueue
    {
        if front + count <= queue.Length
        {
            if obj in queue[front..front + count]
            {
                return true;
            }

        }
        else
        {
            if obj in (queue[front..] + queue[..front + count - queue.Length])
            {
                return true;
            }
        }

        return false;
    }

    method getSize() returns (size: nat) 
        ensures size == |ghostQueue|
    {
        return count;
    }

    method isEmpty() returns (empty: bool) 
        ensures empty <==> |ghostQueue| == 0
    {
        return count == 0;
    }

    method merge(otherQueue: CircularQueue) returns (mergedQueues: CircularQueue)
        ensures |mergedQueues.ghostQueue| == |ghostQueue| + |otherQueue.ghostQueue|
        ensures mergedQueues.ghostQueue == ghostQueue + otherQueue.ghostQueue
        ensures ghostQueue == old(ghostQueue)
        ensures otherQueue.ghostQueue == old(otherQueue.ghostQueue)

    
     
}

method main() {
    var circularQueue := new CircularQueue(2);

    var empty := circularQueue.isEmpty(); assert empty == true;

    circularQueue.enqueue(1);
    circularQueue.enqueue(2);

    var size := circularQueue.getSize(); assert size == 2;

    circularQueue.enqueue(3);

    empty := circularQueue.isEmpty(); assert empty == false;
    size := circularQueue.getSize(); assert size == 3;
    var contains := circularQueue.has(3); 
    assert contains == true;

    var containsFalse := circularQueue.has(10); 
    assert containsFalse == false;

    var x := circularQueue.dequeue(); assert x == 1;
    x := circularQueue.dequeue(); assert x == 2;
    x := circularQueue.dequeue(); assert x == 3;
    
    empty := circularQueue.isEmpty(); assert empty == true;
    size := circularQueue.getSize(); assert size == 0;

    circularQueue.enqueue(1);
    circularQueue.enqueue(2);
    circularQueue.enqueue(3);

    var circularQueue2 := new CircularQueue(2);
    
    circularQueue2.enqueue(11);
    circularQueue2.enqueue(12);

    var mergedQueues := circularQueue.merge(circularQueue2);

    assert mergedQueues.ghostQueue == [1,2,3,11,12];
    assert mergedQueues.ghostQueue != [1,11,12];


}