/*
  Model the execution as action over states in the TLA style.
  This is useful to reason about liveness properties
*/

type Process(==)
const P: set<Process>        // Fixed number of processes in the system
datatype CState = Thinking | Hungry | Eating

/*************************************************/

// State of the ticket system
datatype State = State( ticket: int,
                       serving: int,
                            cs: map<Process, CState>,
                             t: map<Process, int>)

// System initialization
predicate Init(s:State)
{
  && s.cs.Keys == s.t.Keys == P
  && s.ticket == s.serving
  && forall p :: p in P ==> s.cs[p] == Thinking
}

predicate Next(s:State, s':State)
{
  && Inv(s) 
  && exists p :: p in P && NextP(s, p, s')
}

predicate NextP(s:State, p:Process, s':State)
  requires Inv(s) && p in P
{
  Request(s, p, s') || TryEnter(s, p, s') || Leave(s, p, s')
}

predicate Request(s:State, p:Process, s':State)
  requires Inv(s) && p in P
{
  // Activation condition
  && s.cs[p] == Thinking 
  // State update
  && s'.t       == s.t[p := s.ticket]  
  && s'.ticket  == s.ticket + 1
  && s'.cs      == s.cs[p := Hungry]
  // Unchanged State 
  && s'.serving == s.serving            
} 

predicate TryEnter(s:State, p:Process, s':State)
  requires Inv(s) && p in P
{
  // Activation condition  
  && s.cs[p] == Hungry 
  // State update
  && (if s.t[p] == s.serving 
         then s'.cs == s.cs[p := Eating]
         else s'.cs == s.cs)
//   &&    ((s.t[p] == s.serving && s'.cs == s.cs[p := Eating])  // Leino's version
//      ||  (s.t[p] != s.serving && s'.cs == s.cs))
  // Unchanged State   
  && s'.ticket  == s.ticket     
  && s'.serving == s.serving
  && s'.t       == s.t
}

predicate Leave(s:State, p:Process, s':State)
  requires Inv(s) && p in P
{
  // Activation condition 
  && s.cs[p] == Eating 
  // State update
  && s'.serving == s.serving + 1
  && s'.cs == s.cs[p := Thinking]
  // Unchanged State
  && s'.ticket == s.ticket 
  && s'.t == s.t
}

/*************************************************/

// System Invariant 1
// Property that holds at any state.
// Invariante of Inv1 is automatically proven
predicate Inv1(s:State)
{
  && s.cs.Keys == s.t.Keys == P
    // Current number in service is always behind next available number
  && s.serving <= s.ticket
    // Every ticket number held by a process lies in the range from current serving to next ticket 
  && forall p :: p in P && s.cs[p] != Thinking ==> s.serving <= s.t[p] < s.ticket
    // Processes have unique ticket numbers
  && (forall p,q :: 
       (p in P && q in P && p != q && s.cs[p] != Thinking && s.cs[q] != Thinking) 
         ==> (s.t[p] != s.t[q]))
    // The process in the critical section holds the current serving ticket    
  && forall p :: p in P && s.cs[p] == Eating ==> s.t[p] == s.serving
}

predicate TicketIsInUse(s:State, i:int)
  requires s.cs.Keys == s.t.Keys == P
{
  exists p :: p in P && s.cs[p] != Thinking && s.t[p] == i   
}

// System Invariant 2
// For Liveness.   
// Invariante of Inv2 can't be automatically proven
predicate Inv2(s:State)
{ 
  && s.cs.Keys == s.t.Keys == P
  // Every ticket number from s.serving to s.ticket-1 is being used.
  && forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s, i)
} 

// Main system Invariant 
predicate Inv(s:State)
{ 
  Inv1(s) && Inv2(s)
}

// Inv1 is an invariant of the system.
lemma Inv1IsInvariant(s:State, s':State)
  ensures Init(s) ==> Inv1(s)
  ensures Inv1(s) && Next(s, s') ==> Inv1(s')
{ }

// Inv2 is an invariant of the system.
// This proof was ommited in Leino's paper, it can be made shorter,
// however we are stressing here the typical structure of
// an invariante proof which resembles how is also done in TLAPM for TLA+.
lemma Inv2IsInvariant(s:State, s':State)
  ensures Init(s) ==> Inv2(s)
  ensures Inv2(s) && Next(s, s') ==> Inv2(s')
{ 
  if Init(s) {
    assert s.ticket == s.serving;
    assert !exists i :: s.serving <= i < s.ticket;
    assert forall i :: s.serving <= i < s.ticket ==> TicketIsInUse(s, i);
  }  

  if Inv2(s) && Next(s, s') { 
    var p0 :| p0 in P && NextP(s, p0, s');
    if Request(s, p0, s') {
      calc {
             forall i :: s'.serving <= i  <   s'.ticket  ==> TicketIsInUse(s', i);
        <==> (forall i :: s'.serving <= i <= s'.ticket-2 ==> TicketIsInUse(s', i)) && TicketIsInUse(s', s'.ticket-1);
      } 
      assert forall i :: s'.serving <= i <= s'.ticket-2 ==> TicketIsInUse(s', i) by {
        assert s'.ticket == s.ticket + 1;  
        assert s'.serving == s.serving;   
        assert forall i :: s'.serving <= i <= s'.ticket-2 ==> TicketIsInUse(s, i);     
        assert forall i :: s'.serving <= i <= s'.ticket-2 ==> (TicketIsInUse(s, i) ==> TicketIsInUse(s', i));
      }
      assert TicketIsInUse(s', s'.ticket-1);
      assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s', i);
    } else if TryEnter(s, p0, s') {
        assert s'.ticket  == s.ticket;     
        assert s'.serving == s.serving;
        assert s'.t       == s.t;
        if s.t[p0] == s.serving {
          assert forall i :: s'.serving+1 <= i < s'.ticket ==> (TicketIsInUse(s, i) ==> TicketIsInUse(s', i));
          assert forall i :: s'.serving+1 <= i < s'.ticket ==> TicketIsInUse(s', i);      
          assert TicketIsInUse(s', s'.serving); 
          assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s', i); 
        } else { // skip, trivial because nothing changes
          assert s'.cs == s.cs;  
          assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s', i);    
        }
    } else if Leave(s, p0, s') {
      assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s', i) by {
        assert s'.serving == s.serving + 1;  
        assert s'.ticket == s.ticket;   
        assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s, i);     
        assert forall i :: s'.serving <= i < s'.ticket ==> (TicketIsInUse(s, i) ==> TicketIsInUse(s', i));
      }      
      assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s', i);
    } 
    assert s'.cs.Keys == s'.t.Keys == P;
    assert forall i :: s'.serving <= i < s'.ticket ==> TicketIsInUse(s', i);
  }
}  

// Inv is an invariant of the system.
lemma InvIsInvariant(s:State, s':State)
  ensures Init(s) ==> Inv(s)
  ensures Inv(s) && Next(s, s') ==> Inv(s')
{ 
  Inv1IsInvariant(s,s');
  Inv2IsInvariant(s,s');
}  

// Safety property of interest:
//   There can't be more than two philosopers in the kitchen
lemma MutualExclusion(s:State, p:Process, q:Process)
  requires Inv(s) && p in P && q in P
  requires s.cs[p] == Eating && s.cs[q] == Eating
  ensures p == q
{ }

/*************************************************/

// Schedule and Traces of the system

// Define a Schedule, for a set of processes
type Schedule = nat->Process
 
ghost predicate IsSchedule(schedule:Schedule)
{
  forall i :: schedule(i) in P
}

// Define a Trace, for a Schedule
type Trace = nat->State

ghost predicate IsTrace(trace:Trace, schedule:Schedule)
  requires IsSchedule(schedule)
{ 
  // Start in a state satisfying Init
  && Init(trace(0)) 
  // Every pair of consecutive states is allowed as an atomic event by the process scheduled at that time
  && forall i: nat :: && Inv(trace(i)) 
                      && NextP(trace(i), schedule(i), trace(i+1))
}

/*************************************************/

// A schedule is fair if every process occurs infinitely often
// In LTL terms:  ∧_{p∈P}□◇Schedule(p)
// This is unconditional fairness.

ghost predicate FairSchedule(schedule:Schedule)
{
  && IsSchedule(schedule)
  && forall p, n :: p in P ==> HasNext(schedule, p, n)
}

ghost predicate HasNext(schedule:Schedule, p:Process, n:nat)
{
  exists n' :: n <= n' && schedule(n') == p
}

/*************************************************/

// Liveness property

function CurrentlyServedProcess(s:State): Process
  requires Inv(s) && exists p :: p in P && s.cs[p] == Hungry
{
  assert TicketIsInUse(s, s.serving);
  var q :| q in P && s.cs[q] != Thinking && s.t[q] == s.serving;
  q
}

// Find an n' >= n proving
//       that serving is unchanged from time n to time n'
//       that p remains in the same control state and holds the same ticket in n as in n’,
//   and that all hungry processes in n are still still hungry in n' and hold the same ticket in n' as in n.
lemma GetNextStep(trace:Trace, schedule:Schedule, p:Process, n:nat) returns (n':nat)
  requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in P
  requires trace(n).cs[p] != Thinking && trace(n).t[p] == trace(n).serving
  
  ensures n <= n' && schedule(n') == p
  ensures trace(n').serving == trace(n).serving
  ensures trace(n').cs[p]   == trace(n).cs[p]
  ensures trace(n').t[p]    == trace(n).t[p]
  ensures forall q :: q in P && trace(n).cs[q] == Hungry 
            ==> trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q]
{
  assert HasNext(schedule, p, n);
  var u :| n <= u && schedule(u) == p;
  n' := n;
  while schedule(n') != p
    invariant n' <= u
    invariant trace(n').serving == trace(n).serving
    invariant trace(n').cs[p]   == trace(n).cs[p]
    invariant trace(n').t[p]    == trace(n).t[p]
    invariant forall q :: q in P && trace(n).cs[q] == Hungry 
                ==> trace(n').cs[q] == Hungry && trace(n').t[q] == trace(n).t[q]
    decreases u - n'
  {
    n' := n' + 1;
  }
}

// Liveness property of interest: 
//   Every philosopher eventually eats
// In LTL terms:  ∧_{p∈P}□(Hungry(p) => ◇Eating(p))
lemma Liveness(trace:Trace, schedule:Schedule, p:Process, n:nat) returns (n':nat)
  requires FairSchedule(schedule) && IsTrace(trace, schedule) && p in P
  requires trace(n).cs[p] == Hungry
  ensures  n <= n' && trace(n').cs[p] == Eating
{
  n' := n;
  while true
    invariant n <= n' && trace(n').cs[p] == Hungry
    decreases trace(n').t[p] - trace(n').serving
  {
    // find the currently served process and follow it out of the kitchen
    var q := CurrentlyServedProcess(trace(n'));
    if trace(n').cs[q] == Hungry {
      n' := GetNextStep(trace, schedule, q, n');
      n' := n' + 1; // take the step from Hungry to Eating
      if p == q {
        return;
      }
    }
    n' := GetNextStep(trace, schedule, q, n');
    n' := n' + 1; // take the step from Eating to Thinking
  }
}