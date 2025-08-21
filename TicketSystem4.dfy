/*
  The scheduler can record 
    - The history of decisions made, i.e. the schedule.
    - The trace of execution, i.e. the sequence of states.
*/

type Process(==)

datatype CState = Thinking | Hungry | Eating

// We need to define all system operations inside a class so they share the state of the system.
// (we can't do this in a module because we can't define global variables in Dafny)
class TicketSystem
{
  const P: set<Process>        // Fixed number of processes in the system
  var ticket: int              // Next available number in ticket machine
  var serving: int             // Current number for service (ticket display)
  var cs: map<Process, CState> // Current state of each process
  var t: map<Process, int>     // Ticket number for each process

  // System initialization
  constructor (procs:set<Process>)
    ensures Inv()
    ensures P == procs
  {
    P := procs;
    ticket := serving;
    cs := map p | p in procs :: Thinking;
    t  := map p | p in procs :: 0;
  }
 
  method Request(p: Process)
    modifies this
    requires Inv() && p in P && cs[p] == Thinking
    ensures  Inv()
  {
    t, ticket := t[p := ticket], ticket + 1;
    cs := cs[p := Hungry];    
  }

  method Enter(p: Process)
    modifies this  
    requires Inv() && p in P && cs[p] == Hungry && t[p] == serving
    ensures  Inv()
  {
    cs := cs[p := Eating];
  }

  method Leave(p: Process)
    modifies this  
    requires Inv() && p in P && cs[p] == Eating
    ensures  Inv()
  {
    serving := serving + 1;
    cs := cs[p := Thinking];
  }

  /*************************************************/

  // System Invariant
  predicate Inv()
    reads this
  {
    && cs.Keys == t.Keys == P
       // Current number in service is always behind next available number
    && serving <= ticket
       // Every ticket number held by a process lies in the range from current serving to next ticket 
    && forall p :: p in P && cs[p] != Thinking ==> serving <= t[p] < ticket
       // Processes have unique ticket numbers
    && (forall p,q :: 
          (p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking) 
          ==> (t[p] != t[q]))
       // The process in the critical section holds the current serving ticket    
    && (forall p :: p in P && cs[p] == Eating ==> t[p] == serving)      
  }

  // Correctness property:
  // There can't be more than two philosopers in the kitchen
  lemma MutualExclusion(p: Process, q: Process)
    requires Inv() && p in P && q in P
    requires cs[p] == Eating && cs[q] == Eating
    ensures p == q
  {
  }
}

// Specification of the scheduler execution
// The scheduler records schedule and trace
method Run(procs: set<Process>)
  requires procs != {}
  decreases * 
{
  var schedule := [];
  var ts := new TicketSystem(procs);
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];
  while exists p :: p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving)
    invariant ts.Inv()
    decreases *
  {
    // take any process such that it is Thinking, Eating, or Hungry AND READY to enter.
    var p :| p in ts.P && (ts.cs[p] == Hungry ==> ts.t[p] == ts.serving);
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry   => ts.Enter(p); 
      case Eating   => ts.Leave(p);
    }
    schedule := schedule + [p];
    trace := trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
  }
}