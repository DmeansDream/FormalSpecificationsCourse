include "NFCSource.dfy"

module RiderPassModule {
  import opened NFCSourceModule

  class RiderPass extends NFCSource {

    var passId: seq<int>
    var ridesRemaining: int

    predicate Valid()
      reads this
    {
      |passId| == 8 &&
      (forall k :: 0 <= k < 8 ==> 0 <= passId[k] <= 9) &&
      ridesRemaining >= 0
    }

    constructor(pid: seq<int>, rides: int)
      requires |pid| == 8
      requires forall k :: 0 <= k < 8 ==> 0 <= pid[k] <= 9
      requires rides >= 0
      ensures Valid()
      ensures passId == pid
      ensures ridesRemaining == rides
    {
      passId         := pid;
      ridesRemaining := rides;
    }

    function ID(): seq<int>
      reads this
    {
      passId
    }

    function OneRideWorth(): int
      reads this
      ensures OneRideWorth() > 0
    {
      1
    }

    predicate IsValid()
      reads this
    {
      |passId| == 8 &&
      (forall k :: 0 <= k < 8 ==> 0 <= passId[k] <= 9) &&
      ridesRemaining >= 0
    }

    predicate HasSufficientFunds()
      reads this
    {
      ridesRemaining > 0
    }

    function CurrentValue(): int
      reads this
      requires IsValid()
      ensures CurrentValue() >= 0
    {
      ridesRemaining
    }

     method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      
      ensures IsValid()
      ensures OneRideWorth() == old(OneRideWorth()) 
      ensures ridesRemaining == old(ridesRemaining) - 1
      ensures CurrentValue() == old(ridesRemaining) - 1
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())
      ensures ridesRemaining == old(ridesRemaining) - 1
      ensures passId == old(passId)
    {

      ghost var oldPassId   := passId;
      ghost var oldRides    := ridesRemaining;
      ridesRemaining := ridesRemaining - 1;

      assert passId == oldPassId;
      assert |passId| == 8;

      assert forall k :: 0 <= k < 8 ==> 0 <= passId[k] <= 9;
      assert ridesRemaining == oldRides - 1;
      assert ridesRemaining >= 0;

      result := Success;
    }
  }
}
