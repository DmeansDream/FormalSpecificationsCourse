trait BaseValidation
{
    ghost predicate Valid()
        reads this
}

trait NFCSource extends BaseValidation
{
    function Read() : int
        requires Valid()
        reads this
}

trait Pass extends BaseValidation
{
    var rides : int

    function GetRides() : int
        requires Valid()
        reads this
    {
        rides
    }

    method ConsumeRide()
        requires 0 < rides

        requires Valid()
        modifies this
        ensures Valid()

        ensures rides == old(rides) - 1
}

trait Deductable extends BaseValidation
{
    var balance : real

    function GetBal() : real
        requires Valid()
        reads this
    {
        balance
    }
    
    method Deduct(bill : real)
        requires Valid()
        modifies this
        ensures Valid()

        requires 0.0 < bill
        requires bill <= GetBal()

        ensures balance == old(balance) - bill
}

class RiderPass extends NFCSource, Pass
{
    const ID : int

    ghost predicate Valid()   
        reads this
    {
        0 <= rides
    }

    constructor (id : int, rides : int)
        requires 0 <= rides
        ensures Valid()
        ensures this.rides == rides
    {
        ID := id;
        this.rides := rides;
    }

    function Read() : int
        requires Valid()
        reads this
    {
        this.ID
    }

    method ConsumeRide()
        requires 0 < rides

        requires Valid()
        modifies this
        ensures Valid()

        ensures rides == old(rides) - 1
    {
        rides := rides - 1;
    }
}

class PaymentCard extends NFCSource, Deductable
{
    const ID : int

    ghost predicate Valid()   
    reads this
    {
        0.0 <= balance
    }

    constructor (id : int, balance : real)
        ensures Valid()
        requires 0.0 <= balance
        ensures this.balance == balance
    {
        ID := id;
        this.balance := balance;
    }

    function Read() : int
        requires Valid()
        reads this
    {
        this.ID
    }

    method Deduct(bill : real)
        requires Valid()
        modifies this
        ensures Valid()

        requires 0.0 < bill
        requires bill <= GetBal()

        ensures balance == old(balance) - bill
    {
        balance := balance - bill;
    }
}