include "NFCSource.dfy"
// RiderPass.dfy
// Implements a rider pass NFC source.
//
// Formal spec requirements:
//   Req 3:  Pass ID must be exactly 8 digits long
//   Req 4:  Deny if ridesRemaining == 0
//   Req 5:  Deduct exactly 1 ride per transaction
//   Req 6:  ridesRemaining cannot go below 0
//   Req 7:  On failure path, ridesRemaining is unchanged
//   Req 15: Invalid passes (wrong length) are always denied

include "NFCSource.dfy"

module RiderPassModule {
  import opened NFCSourceModule

  class RiderPass extends NFCSource {

    // 8-digit pass number (each element is a decimal digit 0-9)
    var passId: seq<int>

    // How many rides remain on this pass
    var ridesRemaining: int

    // ------------------------------------------------------------------
    // Invariant
    // ------------------------------------------------------------------
    predicate Valid()
      reads this
    {
      |passId| == 8 &&
      (forall k :: 0 <= k < 8 ==> 0 <= passId[k] <= 9) &&
      ridesRemaining >= 0
    }

    // ------------------------------------------------------------------
    // Constructor
    // ------------------------------------------------------------------
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

    // ------------------------------------------------------------------
    // NFCSource trait implementations
    // ------------------------------------------------------------------

    function ID(): seq<int>
      reads this
    {
      passId
    }

    // One ride on a pass costs exactly 1 ride slot
    // Spec req 5: exactly 1 ride worth deducted
    function OneRideWorth(): int
      reads this
      ensures OneRideWorth() > 0
    {
      1
    }

    // Spec req 3, 15: valid iff exactly 8-digit ID with valid digits and rides >= 0
    predicate IsValid()
      reads this
    {
      |passId| == 8 &&
      (forall k :: 0 <= k < 8 ==> 0 <= passId[k] <= 9) &&
      ridesRemaining >= 0
    }

    // Spec req 4: must have at least 1 ride remaining
    predicate HasSufficientFunds()
      reads this
    {
      ridesRemaining > 0
    }

    // Spec req 6: rides remaining always >= 0
    function CurrentValue(): int
      reads this
      requires IsValid()
      ensures CurrentValue() >= 0
    {
      ridesRemaining
    }

    // Spec req 5: deduct exactly 1 ride
    // Spec req 6: ridesRemaining stays >= 0 (guaranteed because HasSufficientFunds requires > 0)
    // Spec req 7: only called on success path
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
      // Snapshot all passId-related invariant facts as ghost variables
      // BEFORE the mutation so Dafny can carry them across the heap update.
      ghost var oldPassId   := passId;
      ghost var oldRides    := ridesRemaining;

      // Spec req 5: deduct exactly 1 ride.
      // Since HasSufficientFunds() ==> ridesRemaining > 0,
      // we get ridesRemaining - 1 >= 0, satisfying spec req 6.
      ridesRemaining := ridesRemaining - 1;

      // Frame reasoning hints:
      //   passId was not assigned in this method body, so passId == oldPassId.
      //   All properties of passId therefore carry over unchanged.
      assert passId == oldPassId;
      assert |passId| == 8;
      // Explicitly assert the digit range forall so Dafny's quantifier
      // instantiation can confirm IsValid() for the passId component.
      assert forall k :: 0 <= k < 8 ==> 0 <= passId[k] <= 9;
      assert ridesRemaining == oldRides - 1;
      assert ridesRemaining >= 0;

      result := Success;
    }
  }
}
