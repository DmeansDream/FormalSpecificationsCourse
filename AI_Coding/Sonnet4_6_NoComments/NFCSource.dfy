module NFCSourceModule {

  datatype DeductResult = Success | Failure

  trait {:termination false} NFCSource {

    function ID(): seq<int>
      reads this

    predicate IsValid()
      reads this

    predicate HasSufficientFunds()
      reads this

    function CurrentValue(): int
      reads this
      requires IsValid()
      ensures CurrentValue() >= 0

    method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      ensures IsValid()
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())
      ensures OneRideWorth() == old(OneRideWorth()) 
      ensures CurrentValue() == old(CurrentValue()) - old(OneRideWorth())

    function OneRideWorth(): int
      reads this
      requires IsValid()
      ensures OneRideWorth() > 0
  }
}
