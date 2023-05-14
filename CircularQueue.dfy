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
        && count <= queue.Length
        && front < queue.Length
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
        //ensures contains(obj)
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
        } 
        else
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

    //ghost predicate contains(item: int)
    //ensures contains(item) == true ==> item in ghostQueue
    //ensures contains(item) == false ==> item !in ghostQueue
    //{
    //    item in ghostQueue
    //}

    method contains(obj: int) returns (contains: bool)
        ensures contains == false ==> forall i :: 0 <= i < queue.Length ==> queue[i] != obj
        ensures contains == true ==> exists j :: 0 <= j < queue.Length && queue[j] == obj
        ensures forall i :: 0 <= i < |ghostQueue| ==> ghostQueue[i] in queue[..]
    {
        var i: nat := 0;
        contains := false;

        while (i < queue.Length)
            decreases queue.Length - i
            invariant 0 <= i <= queue.Length
            invariant forall j :: 0 <= j < i ==> queue[j] != obj
        {
            if (queue[i] == obj) 
            {
                contains := true;
                break;
            }
            i := i + 1;
        }
    }

    method getSize() returns (size: nat) 
        ensures size == |ghostQueue|
    {
        return count;
    }

    method isEmpty() returns (empty: bool) 
        ensures empty == (|ghostQueue| == 0)
    {
        return count == 0;
    }

    // concatena duas filas e retorna uma nova sem alterar a atual
    method concat(otherQueue: CircularQueue) returns (mergedQueues: CircularQueue)
    
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
    size := circularQueue.getSize(); assert size == 5;

    var contains := circularQueue.contains(3); assert contains == true;

    var x := circularQueue.dequeue(); assert x == 1;
    x := circularQueue.dequeue(); assert x == 2;
    x := circularQueue.dequeue(); assert x == 3;
    x := circularQueue.dequeue(); assert x == 4;
    x := circularQueue.dequeue(); assert x == 5;
    
    circularQueue.enqueue(6);
    x := circularQueue.dequeue(); assert x == 6;
}