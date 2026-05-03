include "Validation.dfy"

class RiderPass {
  var id: string
  var rides: nat

  predicate Valid()
    reads this
  {
    IsValidPassId(id)
  }

  constructor(passId: string, initialRides: nat)
    ensures id == passId
    ensures rides == initialRides
  {
    id := passId;
    rides := initialRides;
  }

  method TryUseRide() returns (ok: bool)
    modifies this
    ensures rides >= 0
    ensures ok <==> old(Valid()) && old(rides) > 0
    ensures ok ==> rides + 1 == old(rides)
    ensures !ok ==> rides == old(rides)
  {
    if Valid() && rides > 0 {
      rides := rides - 1;
      ok := true;
    } else {
      ok := false;
    }
  }
}

class PaymentCard {
  var number: string
  var balance: nat

  predicate Valid()
    reads this
  {
    IsValidPaymentNumber(number)
  }

  constructor(cardNumber: string, initialBalance: nat)
    ensures number == cardNumber
    ensures balance == initialBalance
  {
    number := cardNumber;
    balance := initialBalance;
  }

  method TryCharge(amount: nat) returns (ok: bool)
    requires amount > 0
    modifies this
    ensures balance >= 0
    ensures ok <==> old(Valid()) && old(balance) >= amount
    ensures ok ==> balance + amount == old(balance)
    ensures !ok ==> balance == old(balance)
  {
    if Valid() && balance >= amount {
      balance := balance - amount;
      ok := true;
    } else {
      ok := false;
    }
  }
}

datatype NfcSource =
  | PaymentSource(card: PaymentCard)
  | PassSource(pass: RiderPass)
  | UnknownSource