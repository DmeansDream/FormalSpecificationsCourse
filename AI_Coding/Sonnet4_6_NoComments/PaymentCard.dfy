include "NFCSource.dfy"

module PaymentCardModule {
  import opened NFCSourceModule

  function {:fuel 2} LuhnDouble(d: int): int
    requires 0 <= d <= 9
    ensures 0 <= LuhnDouble(d) <= 18
  {
    if d * 2 > 9 then d * 2 - 9 else d * 2
  }

  function {:fuel 20} LuhnSum(digits: seq<int>, fromRight: nat): int
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
    ensures LuhnSum(digits, fromRight) >= 0
    decreases |digits|
  {
    if |digits| == 0 then
      0
    else
      var last := digits[|digits| - 1];
      var contrib := if fromRight % 2 == 1 then LuhnDouble(last) else last;
      contrib + LuhnSum(digits[..|digits| - 1], fromRight + 1)
  }

  predicate LuhnValid(digits: seq<int>)
    requires |digits| == 16
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  {
    LuhnSum(digits, 0) % 10 == 0
  }

  class PaymentCard extends NFCSource {

    var id: seq<int>
    var balance: int
    const fare: int

    predicate Valid()
      reads this
    {
      fare > 0 &&
      balance >= 0 &&
      (|id| != 16 || !(forall k :: 0 <= k < 16 ==> 0 <= id[k] <= 9) || true)
    }

    constructor(cardId: seq<int>, initialBalance: int, rideFare: int)
      requires initialBalance >= 0
      requires rideFare > 0
      ensures Valid()
      ensures balance == initialBalance
      ensures fare == rideFare
      ensures id == cardId
    {
      id      := cardId;
      balance := initialBalance;
      fare    := rideFare;
    }

    function ID(): seq<int>
      reads this
    {
      id
    }

    function OneRideWorth(): int
      reads this
      requires IsValid()
      ensures OneRideWorth() > 0
    {
      fare
    }

    predicate IsValid()
      reads this
    {
      |id| == 16 &&
      (forall k :: 0 <= k < 16 ==> 0 <= id[k] <= 9) &&
      LuhnValid(id) &&
      fare > 0 &&
      balance >= 0
    }

    predicate HasSufficientFunds()
      reads this
    {
      balance >= fare
    }

    function CurrentValue(): int
      reads this
      requires IsValid()
      ensures CurrentValue() >= 0
    {
      balance
    }

    method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      ensures balance == old(balance) - fare
      ensures IsValid()
      ensures CurrentValue() == old(balance) - fare
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())
      ensures balance == old(balance) - fare
      ensures OneRideWorth() == old(OneRideWorth()) 
      ensures id == old(id)
      ensures fare == fare
    {

      ghost var oldId      := id;
      ghost var oldBalance := balance;
      balance := balance - fare;
      
      assert id == oldId;
      assert |id| == 16;
      assert forall k :: 0 <= k < 16 ==> 0 <= id[k] <= 9;

      assert LuhnValid(id);
      assert fare > 0;
      assert balance == oldBalance - fare;
      assert balance >= 0;

      result  := Success;
    }
  }
}
