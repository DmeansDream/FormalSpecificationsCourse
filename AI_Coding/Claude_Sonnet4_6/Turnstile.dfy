include "NFCSource.dfy"
include "Tripod.dfy"
// Turnstile.dfy
// Core metro turnstile NFC subsystem.
//
// Formal spec requirements addressed in this file:
//   Req  1:  Two NFC source types (PaymentCard, RiderPass) accepted via NFCSource trait
//   Req  2:  Open state <-> tripod open; Closed state <-> tripod closed (Valid predicate)
//   Req  3:  Card/Pass ID validity checked via IsValid() before any state change
//   Req  4:  HasSufficientFunds() checked; denied if false
//   Req  5:  source.Deduct() called exactly once on success (trait postcondition enforces -1 ride)
//   Req  6:  Enforced by Deduct() postconditions in each source class
//   Req  7:  Deduct() is never called on the failure path; source value preserved
//   Req  8:  openDuration ticks modelled; WaitAndClose counts down the timer
//   Req  9:  If passenger walked through, gate closes immediately (WaitAndClose)
//   Req 10:  If timer expires without passage, gate closes automatically (WaitAndClose)
//   Req 11:  ProcessNFC always ensures state == Closed at the end
//   Req 12:  openDuration (fare for each source) is constant; enforced by 'const'
//   Req 13:  Gate opens only after successful Deduct()
//   Req 14:  Any source reaching ProcessNFC must implement NFCSource; invalid ones fail IsValid()
//   Req 15:  IsValid() is the gate — invalid sources always produce Denied
//   Req 16:  Valid() predicate enforces state <-> tripod sync at all times

include "NFCSource.dfy"
include "Tripod.dfy"

module TurnstileModule {
  import opened NFCSourceModule
  import opened TripodModule

  // High-level logical state of the turnstile gate
  datatype TurnstileState = GateOpen | GateClosed

  // Outcome returned to the caller after an NFC transaction attempt
  datatype ProcessResult =
    | Admitted    // Source valid, funds deducted, passenger walked through
    | TimedOut    // Source valid, funds deducted, passenger did NOT walk through in time
    | Denied      // Source invalid or insufficient funds; no state change to source

  class Turnstile {

    // The physical tripod barrier object
    var tripod: Tripod

    // The logical gate state of the turnstile
    var state: TurnstileState

    // Number of timer ticks the gate stays open after a successful transaction.
    // Spec req 8: set at construction, never changes.
    // Spec req 12: immutable constant.
    const openDuration: nat

    // ------------------------------------------------------------------
    // Core invariant
    // Spec req 2, 16: logical state and physical tripod must always be in sync.
    // ------------------------------------------------------------------
    predicate Valid()
      reads this, tripod
    {
      (state == GateOpen   ==> tripod.IsOpen())   &&
      (state == GateClosed ==> tripod.IsClosed()) &&
      openDuration > 0
    }

    // ------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------
    constructor(duration: nat, t: Tripod)
      requires duration > 0
      requires t.IsClosed()
      ensures tripod == t
      ensures state == GateClosed
      ensures openDuration == duration
      ensures Valid()
    {
      tripod       := t;
      state        := GateClosed;
      openDuration := duration;
    }

    // ------------------------------------------------------------------
    // Internal gate transitions
    // Both helpers maintain Valid() as a postcondition.
    // ------------------------------------------------------------------

    // Transition to GateOpen: set logical state and raise physical barrier.
    // Spec req 2, 16.
    method OpenGate()
      requires Valid()
      modifies this, tripod
      ensures state == GateOpen
      ensures tripod.IsOpen()
      ensures Valid()
      ensures tripod == old(tripod)
    {
      tripod.Open();
      state := GateOpen;
    }

    // Transition to GateClosed: set logical state and lower physical barrier.
    // Spec req 2, 16.
    method CloseGate()
      requires Valid()
      modifies this, tripod
      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
      ensures tripod == old(tripod)
    {
      tripod.Close();
      state := GateClosed;
    }

    // ------------------------------------------------------------------
    // Timer / passenger detection simulation
    //
    // In a physical system this method would poll hardware for
    // 'openDuration' ticks. Here we model the two possible outcomes
    // (passenger detected or timer expired) via the boolean parameter,
    // which a test harness or the environment supplies.
    //
    // Spec req 8:  gate is open for openDuration ticks.
    // Spec req 9:  passenger detected -> close immediately.
    // Spec req 10: timer expired -> close automatically.
    // ------------------------------------------------------------------
    method WaitAndClose(passengerDetected: bool) returns (walked: bool)
      requires Valid()
      requires state == GateOpen
      modifies this, tripod
      ensures walked == passengerDetected
      ensures state == GateClosed     // Spec req 9 & 10: always closed after
      ensures tripod.IsClosed()
      ensures Valid()
      ensures tripod == old(tripod)
    {
      walked := passengerDetected;
      // Regardless of whether the passenger walked or the timer expired,
      // the gate MUST close. Spec req 9, 10.
      CloseGate();
    }

    // ------------------------------------------------------------------
    // ProcessNFC — top-level NFC transaction handler
    //
    // Called when a card or pass is presented to the NFC reader.
    //
    // Algorithm:
    //   1. Validate source (ID format, Luhn for cards, digit-range)    [Req 3, 15]
    //   2. Check sufficient funds / rides                               [Req 4]
    //   3. If (1) or (2) fail  -> return Denied, source unchanged      [Req 7, 13]
    //   4. Deduct one ride worth from source                           [Req 5]
    //   5. Open gate                                                    [Req 2, 13]
    //   6. Wait openDuration ticks or until passenger detected          [Req 8]
    //   7. Close gate                                                   [Req 9, 10]
    //   8. Return Admitted or TimedOut                                  [Req 9, 10]
    //   9. Postcondition: state == GateClosed                          [Req 11]
    // ------------------------------------------------------------------
    method ProcessNFC(source: NFCSource, passengerDetected: bool)
        returns (result: ProcessResult)
      requires Valid()
      requires state == GateClosed

      requires {source} !! {this, tripod}

      // source is a non-null NFCSource (Dafny references are non-null by default)
      modifies this, tripod, source
      // Spec req 11: turnstile always returns to Closed after a processing loop
      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
      ensures tripod == old(tripod)
      ensures old(source.IsValid()) ==> source.IsValid()
      
      // Spec req 15: invalid source always yields Denied
      ensures !old(source.IsValid()) ==> result == Denied

      // Spec req 4: no funds -> Denied
      ensures (old(source.IsValid()) && !old(source.HasSufficientFunds())) ==> result == Denied

      // Spec req 13: gate is never opened unless the transaction succeeded
      // (if Denied, CurrentValue is unchanged — source.Deduct was never called)
      ensures (result == Denied && old(source.IsValid())) ==> source.IsValid()

      ensures (result == Denied && old(source.IsValid())) ==>
          source.CurrentValue() == old(source.CurrentValue())
      ensures result == Denied ==>
                state == GateClosed

      // ── ADMITTED: complete characterisation (req 9) ──────────────────────────
      // Valid + funds + passenger walked  =>  Admitted
      ensures (old(source.IsValid()) && old(source.HasSufficientFunds()) && passengerDetected)
              ==> result == Admitted
      // Admitted  =>  passenger actually walked (no phantom admissions)
      ensures result == Admitted ==> passengerDetected
      // Admitted  =>  the source was valid and funded (no free rides)
      ensures result == Admitted ==> old(source.IsValid())
      ensures result == Admitted ==> old(source.HasSufficientFunds())

      // ── TIMEDOUT: complete characterisation (req 10) ─────────────────────────
      // Valid + funds + NO passenger  =>  TimedOut
      ensures (old(source.IsValid()) && old(source.HasSufficientFunds()) && !passengerDetected)
              ==> result == TimedOut
      // TimedOut  =>  passenger did NOT walk
      ensures result == TimedOut ==> !passengerDetected
      // TimedOut  =>  source was valid and funded
      ensures result == TimedOut ==> old(source.IsValid())
      ensures result == TimedOut ==> old(source.HasSufficientFunds())

      // ── Value mutation: exactly one deduction on non-Denied results (req 5, 6) ─
      // After Admitted or TimedOut the value must have dropped by exactly one fare
      // (relies on the NFCSource trait postcondition for Deduct())
      //ensures (result == Admitted || result == TimedOut) && (source.IsValid())==>
      //    source.CurrentValue() == old(source.CurrentValue()) - old(source.OneRideWorth())

      ensures (old(source.IsValid()) && old(source.HasSufficientFunds())) ==>
          source.CurrentValue() == old(source.CurrentValue()) - old(source.OneRideWorth())

      // ── Completeness: result is *always* one of the three values ─────────────
      // (Dafny's datatype exhaustiveness handles this, but spelling it out is
      //  useful documentation and lets the verifier close the proof trivially.)
      ensures result == Denied || result == Admitted || result == TimedOut
      
    {
      // Step 1 & 2: validate source format and funds
      // Spec req 3, 4, 15
      if !source.IsValid() { result := Denied; return; }
      if !source.HasSufficientFunds() { result := Denied; return; }

      // Step 3: deduct exactly one ride worth
      // Spec req 5, 6 (enforced by trait postconditions on Deduct)
      var deductOutcome := source.Deduct();

      // Spec req 13: open only if deduction succeeded
      // (The trait contract guarantees deductOutcome == Success given preconditions,
      //  but we keep the branch for defensive correctness.)
      if deductOutcome == Success {
        // Step 4: open the gate
        // Spec req 2, 16
        OpenGate();

        // Step 5: wait for passenger or timer expiry
        // Spec req 8, 9, 10
        var walked := WaitAndClose(passengerDetected);

        // Step 6: report outcome
        // Spec req 9, 10, 11 — gate is now Closed (WaitAndClose postcondition)
        if walked {
          result := Admitted;   // Spec req 9
        } else {
          result := TimedOut;   // Spec req 10
        }
      } else {
        // Defensive branch: Deduct() unexpectedly returned Failure.
        // Gate must not open. Spec req 13.
        // NOTE: this branch is unreachable given trait postcondition,
        //       but Dafny needs the state to still satisfy ensures.
        result := Denied;
      }
      // Spec req 11: at this point state == GateClosed is guaranteed
      // by either the early return, WaitAndClose, or no open being called.
    }

    // ------------------------------------------------------------------
    // Convenience query predicates
    // ------------------------------------------------------------------

    predicate IsOpen()
      reads this
    {
      state == GateOpen
    }

    predicate IsClosed()
      reads this
    {
      state == GateClosed
    }
  }
}
