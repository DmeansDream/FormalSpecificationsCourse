include "Sources.dfy"

datatype TurnstileState =
  | Open
  | Closed

class Turnstile {
  const fare: nat
  var state: TurnstileState
  var tripodOpen: bool
  var openTicksRemaining: nat

  predicate StateConsistent()
    reads this
  {
    fare > 0 &&
    (tripodOpen <==> state == Open) &&
    (state == Open ==> openTicksRemaining > 0) &&
    (state == Closed ==> openTicksRemaining == 0)
  }

  constructor(initialFare: nat) 
    requires initialFare > 0
    ensures fare == initialFare
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures StateConsistent()
  {
    fare := initialFare;
    state := Closed;
    tripodOpen := false;
    openTicksRemaining := 0;
  }

  function SourceObjects(src: NfcSource): set<object>
  {
    match src
    case PaymentSource(card) => {card}
    case PassSource(pass) => {pass}
    case UnknownSource => {}
  }

  method AttemptTransaction(src: NfcSource) returns (success: bool)
    requires StateConsistent()
    modifies SourceObjects(src)
    ensures StateConsistent()
    ensures match src
      case PaymentSource(card) => success <==> old(card.Valid()) && old(card.balance) >= fare
      case PassSource(pass) => success <==> old(pass.Valid()) && old(pass.rides) > 0
      case UnknownSource => !success
    ensures match src
      case PaymentSource(card) => !success ==> card.balance == old(card.balance)
      case PassSource(pass) => !success ==> pass.rides == old(pass.rides)
      case UnknownSource => true
    ensures match src
      case PaymentSource(card) => success ==> card.balance + fare == old(card.balance)
      case PassSource(pass) => success ==> pass.rides + 1 == old(pass.rides)
      case UnknownSource => true
  {
    match src
    case PaymentSource(card) =>
      success := card.TryCharge(fare);
    case PassSource(pass) =>
      success := pass.TryUseRide();
    case UnknownSource =>
      success := false;
  }

  method Close()
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
  {
    state := Closed;
    tripodOpen := false;
    openTicksRemaining := 0;
  }

  method OpenForTicks(ticks: nat)
    requires ticks > 0
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures state == Open
    ensures tripodOpen
    ensures openTicksRemaining == ticks
  {
    state := Open;
    tripodOpen := true;
    openTicksRemaining := ticks;
  }

  method PassengerPassed()
    requires state == Open
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
  {
    Close();
  }

  method Tick()
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
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

  method ProcessSource(src: NfcSource, passengerWalked: bool, timeoutTicks: nat) returns (result: bool)
    requires timeoutTicks > 0
    requires StateConsistent()
    modifies this, SourceObjects(src)
    ensures StateConsistent()
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures match src
      case PaymentSource(card) => result <==> old(card.Valid()) && old(card.balance) >= fare
      case PassSource(pass) => result <==> old(pass.Valid()) && old(pass.rides) > 0
      case UnknownSource => !result
    ensures match src
      case PaymentSource(card) => !result ==> card.balance == old(card.balance)
      case PassSource(pass) => !result ==> pass.rides == old(pass.rides)
      case UnknownSource => true
    ensures match src
      case PaymentSource(card) => result ==> card.balance + fare == old(card.balance)
      case PassSource(pass) => result ==> pass.rides + 1 == old(pass.rides)
      case UnknownSource => true
  {
    match src
    case PaymentSource(card) =>
      var valid0 := card.Valid();
      var bal0 := card.balance;
      result := AttemptTransaction(src);
      assert result <==> valid0 && bal0 >= fare;

      if result {
        assert card.balance + fare == bal0;
        OpenForTicks(timeoutTicks);
        if passengerWalked {
          PassengerPassed();
        } else {
          while state == Open
            modifies this
            decreases openTicksRemaining
            invariant StateConsistent()
          {
            Tick();
          }
        }
      } else {
        assert card.balance == bal0;
        Close();
      }

      if result {
        assert card.balance + fare == bal0;
      } else {
        assert card.balance == bal0;
      }

    case PassSource(pass) =>
      var valid0 := pass.Valid();
      var rides0 := pass.rides;
      result := AttemptTransaction(src);
      assert result <==> valid0 && rides0 > 0;

      if result {
        assert pass.rides + 1 == rides0;
        OpenForTicks(timeoutTicks);
        if passengerWalked {
          PassengerPassed();
        } else {
          while state == Open
            modifies this
            decreases openTicksRemaining
            invariant StateConsistent()
          {
            Tick();
          }
        }
      } else {
        assert pass.rides == rides0;
        Close();
      }

      if result {
        assert pass.rides + 1 == rides0;
      } else {
        assert pass.rides == rides0;
      }

    case UnknownSource =>
      result := AttemptTransaction(src);
      assert !result;
      Close();
  }

}