module TripodModule {

  datatype TripodState = TripodOpen | TripodClosed

  class Tripod {

    var state: TripodState

    predicate Valid()
      reads this
    {
      state == TripodOpen || state == TripodClosed
    }

    constructor()
      ensures state == TripodClosed
      ensures Valid()
    {
      state := TripodClosed;
    }

    method Open()
      modifies this
      ensures state == TripodOpen
      ensures Valid()
    {
      state := TripodOpen;
    }

    method Close()
      modifies this
      ensures state == TripodClosed
      ensures Valid()
    {
      state := TripodClosed;
    }

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
