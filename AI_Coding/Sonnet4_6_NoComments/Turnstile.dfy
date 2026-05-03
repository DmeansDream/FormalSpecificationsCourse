include "NFCSource.dfy"
include "Tripod.dfy"

module TurnstileModule {
  import opened NFCSourceModule
  import opened TripodModule

  datatype TurnstileState = GateOpen | GateClosed

  datatype ProcessResult =
    | Admitted    // Source valid, funds deducted, passenger walked through
    | TimedOut    // Source valid, funds deducted, passenger did NOT walk through in time
    | Denied      // Source invalid or insufficient funds; no state change to source

  class Turnstile {

    const tripod: Tripod
    var state: TurnstileState
    const openDuration: nat

    predicate Valid()
      reads this, tripod
    {
      (state == GateOpen   ==> tripod.IsOpen())   &&
      (state == GateClosed ==> tripod.IsClosed()) &&
      openDuration > 0
    }

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

    method OpenGate()
      requires Valid()
      modifies this, tripod
      ensures state == GateOpen
      ensures tripod.IsOpen()
      ensures Valid()
    {
      tripod.Open();
      state := GateOpen;
    }

    method CloseGate()
      requires Valid()
      modifies this, tripod
      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
    {
      tripod.Close();
      state := GateClosed;
    }

    method WaitAndClose(passengerDetected: bool) returns (walked: bool)
      requires Valid()
      requires state == GateOpen
      modifies this, tripod
      ensures walked == passengerDetected
      ensures state == GateClosed     
      ensures tripod.IsClosed()
      ensures Valid()
    {
      walked := passengerDetected;
      CloseGate();
    }

    method ProcessNFC(source: NFCSource, passengerDetected: bool)
        returns (result: ProcessResult)
      requires Valid()
      requires state == GateClosed

      requires {source} !! {this, tripod}
      modifies this, tripod, source

      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
      ensures old(source.IsValid()) ==> source.IsValid()
      
      ensures !old(source.IsValid()) ==> result == Denied
      ensures (old(source.IsValid()) && !old(source.HasSufficientFunds())) ==> result == Denied
      ensures (result == Denied && old(source.IsValid())) ==> source.IsValid()

      ensures (result == Denied && old(source.IsValid())) ==>
          source.CurrentValue() == old(source.CurrentValue())
      ensures result == Denied ==>
                state == GateClosed

      ensures (old(source.IsValid()) && old(source.HasSufficientFunds()) && passengerDetected)
              ==> result == Admitted
      ensures result == Admitted ==> passengerDetected
      ensures result == Admitted ==> old(source.IsValid())
      ensures result == Admitted ==> old(source.HasSufficientFunds())

      ensures (old(source.IsValid()) && old(source.HasSufficientFunds()) && !passengerDetected)
              ==> result == TimedOut
      ensures result == TimedOut ==> !passengerDetected
      ensures result == TimedOut ==> old(source.IsValid())
      ensures result == TimedOut ==> old(source.HasSufficientFunds())

      ensures (old(source.IsValid()) && old(source.HasSufficientFunds())) ==>
          source.CurrentValue() == old(source.CurrentValue()) - old(source.OneRideWorth())

      ensures result == Denied || result == Admitted || result == TimedOut 
    {
      if !source.IsValid() { result := Denied; return; }
      if !source.HasSufficientFunds() { result := Denied; return; }
      var deductOutcome := source.Deduct();

      if deductOutcome == Success {
        OpenGate();

        var walked := WaitAndClose(passengerDetected);

        if walked {
          result := Admitted;   
        } else {
          result := TimedOut;   
        }
      } else {
        result := Denied;
      }

    }

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
