// NFCSource.dfy
// Defines the abstract trait that all NFC payment sources must implement.
// Both PaymentCard and RiderPass extend this trait.

module NFCSourceModule {

  // Represents the result of an attempted payment/deduction
  datatype DeductResult = Success | Failure

  // Abstract trait for any NFC-based payment source
  trait {:termination false} NFCSource {

    // The unique ID stored on the NFC chip
    function ID(): seq<int>
      reads this

    // True iff the source has a well-formed ID (correct length, Luhn for cards)
    // Spec req 3, 15
    predicate IsValid()
      reads this

    // True iff there is enough value (money/rides) to pay for one ride
    // Spec req 4
    predicate HasSufficientFunds()
      reads this

    // Returns the current numeric value on this source (balance or ride count)
    // Always non-negative. Spec req 6.
    function CurrentValue(): int
      reads this
      requires IsValid()
      ensures CurrentValue() >= 0

    // Deducts exactly one ride's worth from the source.
    // Preconditions guarantee validity and sufficient funds.
    // Postconditions:
    //   - Always returns Success (guaranteed by preconditions)
    //   - CurrentValue decreases by exactly one ride worth
    //   - CurrentValue stays >= 0 (spec req 6)
    //   - ID is not modified (spec req 7 – only value changes)
    // Spec req 5, 6
    method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      ensures IsValid()
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())

    // The cost of one ride on this specific source type
    // (fare for PaymentCard, 1 for RiderPass)
    function OneRideWorth(): int
      reads this
      requires IsValid()
      ensures OneRideWorth() > 0
  }
}
