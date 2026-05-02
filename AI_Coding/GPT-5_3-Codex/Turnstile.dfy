//include "Sources.dfy"

datatype TurnstileState =
  | Open
  | Closed

class Turnstile {
  var fare: nat
  var state: TurnstileState
  var tripodOpen: bool
  var openTicksRemaining: nat

  invariant fare > 0.0
  invariant tripodOpen <==> state == Open
  invariant state == Open ==> openTicksRemaining > 0

  constructor(initialFare: nat)
    requires initialFare > 0
    ensures fare == initialFare
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
  {
    fare := initialFare;
    state := Closed;
    tripodOpen := false;
    openTicksRemaining := 0;
  }

  function method SourceObjects(src: NfcSource): set<object>
  {
    match src
    case PaymentSource(card) => {card}
    case PassSource(pass) => {pass}
    case UnknownSource => {}
  }

  method AttemptTransaction(src: NfcSource) returns (success: bool)
    modifies SourceObjects(src)
    ensures src.UnknownSource? ==> !success
    ensures src.PaymentSource? && !success ==> src.card.balance == old(src.card.balance)
    ensures src.PassSource? && !success ==> src.pass.rides == old(src.pass.rides)
    ensures src.PaymentSource? && success ==> src.card.balance + fare == old(src.card.balance)
    ensures src.PassSource? && success ==> src.pass.rides + 1 == old(src.pass.rides)
  {
    match src
    case PaymentSource(card) =>
      success := card.TryCharge(fare)
    case PassSource(pass) =>
      success := pass.TryUseRide()
    case UnknownSource =>
      success := false
  }

  method Close()
    modifies this
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures fare == old(fare)
  {
    state := Closed;
    tripodOpen := false;
    openTicksRemaining := 0;
  }

  method OpenForTicks(ticks: nat)
    requires ticks > 0
    modifies this
    ensures state == Open
    ensures tripodOpen
    ensures openTicksRemaining == ticks
    ensures fare == old(fare)
  {
    state := Open;
    tripodOpen := true;
    openTicksRemaining := ticks;
  }

  method PassengerPassed()
    requires state == Open
    modifies this
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures fare == old(fare)
  {
    Close();
  }

  method Tick()
    modifies this
    ensures fare == old(fare)
    ensures old(state) == Closed ==> state == Closed
    ensures old(state) == Open ==> state == Closed || openTicksRemaining < old(openTicksRemaining)
  {
    if state == Open {
      if openTicksRemaining > 1 {
        openTicksRemaining := openTicksRemaining - 1;
      } else {
        Close();
      }
    }
  }

  method ProcessSource(src: NfcSource, passengerWalked: bool, timeoutTicks: nat) returns (opened: bool)
    requires timeoutTicks > 0
    modifies this, SourceObjects(src)
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures fare == old(fare)
    ensures src.UnknownSource? ==> !opened
    ensures src.PaymentSource? && !opened ==> src.card.balance == old(src.card.balance)
    ensures src.PassSource? && !opened ==> src.pass.rides == old(src.pass.rides)
  {
    opened := AttemptTransaction(src);

    if opened {
      OpenForTicks(timeoutTicks);

      if passengerWalked {
        PassengerPassed();
      } else {
        while state == Open
          decreases openTicksRemaining
          invariant fare > 0
          invariant tripodOpen <==> state == Open
          invariant state == Open ==> openTicksRemaining > 0
        {
          Tick();
        }
      }
    } else {
      Close();
    }
  }
}