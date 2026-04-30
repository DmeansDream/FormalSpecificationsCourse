// Tripod.dfy
// Models the physical tripod barrier of the metro turnstile.
//
// Formal spec requirements:
//   Req  2: If turnstile state is Open, tripod must be open; if Closed, tripod must be closed
//   Req 16: System state and tripod state always remain in sync
//
// The Tripod class is intentionally minimal: it is solely responsible for
// tracking and transitioning its physical state. Sync invariants are
// enforced by the Turnstile class which owns both objects.

module TripodModule {

  // Physical state of the tripod barrier
  datatype TripodState = TripodOpen | TripodClosed

  class Tripod {

    var state: TripodState

    // The tripod is always in one of exactly two valid states
    predicate Valid()
      reads this
    {
      state == TripodOpen || state == TripodClosed
    }

    // Construct in the closed (safe) position
    constructor()
      ensures state == TripodClosed
      ensures Valid()
    {
      state := TripodClosed;
    }

    // Raise the barrier arm to allow passage
    method Open()
      modifies this
      ensures state == TripodOpen
      ensures Valid()
    {
      state := TripodOpen;
    }

    // Lower the barrier arm to block passage
    method Close()
      modifies this
      ensures state == TripodClosed
      ensures Valid()
    {
      state := TripodClosed;
    }

    // Query predicates — used by Turnstile for sync invariant
    predicate IsOpen()
      reads this
    {
      state == TripodOpen
    }

    predicate IsClosed()
      reads this
    {
      state == TripodClosed
    }
  }
}
