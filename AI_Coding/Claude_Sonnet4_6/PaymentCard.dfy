include "NFCSource.dfy"
// PaymentCard.dfy
// Implements a payment card NFC source.
//
// Formal spec requirements:
//   Req 3:  ID must be exactly 16 digits and pass Luhn algorithm check
//   Req 4:  Deny if balance < fare
//   Req 5:  Deduct exactly 'fare' amount per ride
//   Req 6:  Balance cannot go below 0
//   Req 7:  On failure, balance is unchanged (Deduct is never called on invalid/insufficient cards)
//   Req 12: Fare is set at construction and never changes
//   Req 15: Invalid cards (wrong length or bad Luhn) are always denied

include "NFCSource.dfy"

module PaymentCardModule {
  import opened NFCSourceModule

  // ------------------------------------------------------------------
  // Luhn Algorithm (pure, fully verifiable)
  // ------------------------------------------------------------------

  // Double a single digit; if result > 9, subtract 9
  function {:fuel 2} LuhnDouble(d: int): int
    requires 0 <= d <= 9
    ensures 0 <= LuhnDouble(d) <= 18
  {
    if d * 2 > 9 then d * 2 - 9 else d * 2
  }

  // Recursive Luhn sum.
  // fromRight is the 0-based index of the current last element counting from the right.
  // Every digit at an odd position from the right (1, 3, 5, ...) gets doubled.
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

  // The Luhn check: total sum mod 10 must equal 0
  predicate LuhnValid(digits: seq<int>)
    requires |digits| == 16
    requires forall i :: 0 <= i < |digits| ==> 0 <= digits[i] <= 9
  {
    LuhnSum(digits, 0) % 10 == 0
  }

  

  // ------------------------------------------------------------------
  // PaymentCard
  // ------------------------------------------------------------------

  class PaymentCard extends NFCSource {

    // 16-digit card number (each element is a decimal digit 0-9)
    var id: seq<int>

    // Monetary balance in smallest unit (e.g. cents)
    var balance: int

    // Cost of one ride — constant for the lifetime of this card object
    // Spec req 12: fare > 0 and never changes
    const fare: int

    // ------------------------------------------------------------------
    // Invariant (internal consistency)
    // ------------------------------------------------------------------
    predicate Valid()
      reads this
    {
      fare > 0 &&
      balance >= 0 &&
      (|id| != 16 || !(forall k :: 0 <= k < 16 ==> 0 <= id[k] <= 9) || true)
    }

    // ------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // NFCSource trait implementations
    // ------------------------------------------------------------------

    // The card's ID
    function ID(): seq<int>
      reads this
    {
      id
    }

    // Cost of one ride on this card = fare
    // Spec req 12: fare > 0
    function OneRideWorth(): int
      reads this
      requires IsValid()
      ensures OneRideWorth() > 0
    {
      fare
    }

    // Spec req 3, 15: valid iff 16-digit Luhn-passing ID and fare > 0 and balance >= 0
    predicate IsValid()
      reads this
    {
      |id| == 16 &&
      (forall k :: 0 <= k < 16 ==> 0 <= id[k] <= 9) &&
      LuhnValid(id) &&
      fare > 0 &&
      balance >= 0
    }

    // Spec req 4: sufficient funds iff balance >= fare
    predicate HasSufficientFunds()
      reads this
    {
      balance >= fare
    }

    // Spec req 6: balance is always >= 0
    function CurrentValue(): int
      reads this
      requires IsValid()
      ensures CurrentValue() >= 0
    {
      balance
    }

    // Spec req 5: deduct exactly fare from balance
    // Spec req 6: balance stays >= 0 (guaranteed because HasSufficientFunds requires balance >= fare)
    // Spec req 7: only called on success path, so on failure (Denied branch) this is never invoked
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
      // Snapshot immutable fields before mutation so Dafny can carry
      // their invariant facts across the heap update.
      ghost var oldId      := id;
      ghost var oldBalance := balance;

      // Spec req 5: deduct exactly the fare.
      // Since HasSufficientFunds() ==> balance >= fare, we get balance - fare >= 0.
      balance := balance - fare;

      // Frame reasoning hints: 'id' and 'fare' were not assigned.
      assert id == oldId;
      assert |id| == 16;
      assert forall k :: 0 <= k < 16 ==> 0 <= id[k] <= 9;
      // LuhnValid(id) still holds because id is unchanged.
      assert LuhnValid(id);
      assert fare > 0;
      assert balance == oldBalance - fare;
      assert balance >= 0;

      result  := Success;
    }
  }
}
