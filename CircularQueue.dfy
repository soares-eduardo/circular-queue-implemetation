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
    var count: nat; // number of elements
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
        ensures obj in ghostQueue
        ensures ghostQueue == old(ghostQueue) + [obj]
        ensures |ghostQueue| == old(|ghostQueue|) + 1
    {
        // queue is full?
        if count == queue.Length 
        { 
            var double := queue.Length;
            var newQueue := new int[queue.Length + double];
            
            // index bigger than start? move objs up to 2nd half
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

    method concat(otherQueue: CircularQueue) returns (mergedQueues: CircularQueue)
        requires otherQueue.Valid()
        requires |otherQueue.ghostQueue| > 0
        ensures mergedQueues.ghostQueue == ghostQueue + otherQueue.ghostQueue
        ensures |mergedQueues.ghostQueue| == |ghostQueue| + |otherQueue.ghostQueue|
        ensures ghostQueue == old(ghostQueue)
    {
        var otherQueueSize: nat := otherQueue.getSize();
        mergedQueues := new CircularQueue(count + otherQueueSize);

        var i: nat := 0;
        while i < count
            decreases count - i
        { 
            var a: nat := if front == queue.Length - 1 then 0 else front + 1;
            //mergedQueues.enqueue(queue[a]);
            i := i + 1;
        }

        i := 0;
        while i < otherQueueSize
            decreases otherQueueSize - i
        {
            //var obj: int := otherQueue.dequeue();
            //mergedQueues.enqueue(obj);
            i := i + 1;
        }
        
        mergedQueues.ghostQueue := ghostQueue + otherQueue.ghostQueue;
    }

    /*method Merge(other: CircularQueue) returns (result: CircularQueue)
        requires Valid()
        requires other.Valid()
    {
        result := new CircularQueue(queue.Length);
        
        var tempQueue: seq<int> := new seq[queue.Length];
        var tempFront := 0;
        var tempCount := 0;
        
        var mergedGhostQueue: seq<int> := ghostQueue + other.ghostQueue;
        
        if count + other.count <= queue.Length {
            // Merging without wrapping around
            tempQueue[tempCount..tempCount + count] := queue[front..front + count];
            tempCount := tempCount + count;
            tempQueue[tempCount..tempCount + other.count] := other.queue[other.front..other.front + other.count];
            tempCount := tempCount + other.count;
        } else {
            // Merging with wrapping around
            var remainingSpace := queue.Length - count;
            tempQueue[tempCount..tempCount + count] := queue[front..];
            tempCount := tempCount + count;
            tempQueue[tempCount..tempCount + remainingSpace] := queue[..remainingSpace];
            tempCount := tempCount + remainingSpace;
            
            var remainingElements := other.count - remainingSpace;
            tempQueue[tempCount..tempCount + remainingSpace] := other.queue[other.front..];
            tempCount := tempCount + remainingSpace;
            tempQueue[tempCount..tempCount + remainingElements] := other.queue[..remainingElements];
            tempCount := tempCount + remainingElements;
        }
        
        result.queue := tempQueue;
        result.front := tempFront;
        result.count := tempCount;
        result.ghostQueue := mergedGhostQueue;
    }*/
}

method main() {
    var circularQueue := new CircularQueue(2);

    var empty := circularQueue.isEmpty(); assert empty == true;

    circularQueue.enqueue(1);
    circularQueue.enqueue(2);

    var size := circularQueue.getSize(); assert size == 2;

    circularQueue.enqueue(3);
    circularQueue.enqueue(4);
    circularQueue.enqueue(5);

    empty := circularQueue.isEmpty(); assert empty == false;
    size := circularQueue.getSize(); assert size == 5;
    
    var contains := circularQueue.has(3); 
    assert contains == true;

    var containsFalse := circularQueue.has(10); 
    assert containsFalse == false;

    var x := circularQueue.dequeue(); assert x == 1;
    x := circularQueue.dequeue(); assert x == 2;
    x := circularQueue.dequeue(); assert x == 3;
    x := circularQueue.dequeue(); assert x == 4;
    x := circularQueue.dequeue(); assert x == 5;
    
    empty := circularQueue.isEmpty(); assert empty == true;
    size := circularQueue.getSize(); assert size == 0;

    circularQueue.enqueue(6);
    x := circularQueue.dequeue(); assert x == 6;
}