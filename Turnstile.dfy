include "CardClasses.dfy"

datatype State = Boot | Closed | Open | Processing

const tickCount : int := 1000
const PersonTick : int := 200

class Turnstile
{
    var state : State
    var gate : bool
    var bill : real

    var timerTicks : int
    var personPassed : bool

    ghost predicate Valid()   
        reads this
    {
        (state == Open ==> gate == true ==> timerTicks > 0 || personPassed) &&
        (state == Closed ==> gate == false ==> timerTicks == 0) &&
        (state == Boot ==> gate == false ==> timerTicks == 0) &&
        (state == Processing ==> gate == false ==> timerTicks == 0) &&
        0.0 < bill
    }

    constructor (state : State, Payment : real)
        requires state == Boot
        requires 0.0 < Payment
        ensures Valid()
        ensures this.state == state
        ensures this.bill == Payment
    {
        this.state := state;
        this.bill := Payment;

        this.gate := false;
        this.timerTicks := 0;
        this.personPassed := false;
    }

    method Initialize()
        requires Valid()
        modifies this
        ensures Valid()

        requires this.state == Boot
        ensures this.state == Closed
        ensures this.bill == old(this.bill)
    {
        this.gate := false;
        this.timerTicks := 0;
        this.personPassed := false;
        this.state := Closed;
    }

    method ProcessNFCSource(source : NFCSource) returns (res : bool)
        requires Valid()
        modifies this, source
        ensures Valid()

        requires source.Valid()
        ensures source.Valid()

        requires this.state == Closed
        requires 0.0 < bill
        ensures this.state == Closed
        ensures bill == old(bill)

        ensures res ==> source is RiderPass ==> (source as RiderPass).rides == old((source as RiderPass).rides) - 1
        ensures res ==> source is PaymentCard ==> (source as PaymentCard).balance == old((source as PaymentCard).balance) - bill

        ensures !res ==> source is RiderPass ==> (source as RiderPass).rides == old((source as RiderPass).rides)
        ensures !res ==> source is PaymentCard ==> (source as PaymentCard).balance == old((source as PaymentCard).balance)
    {
        
        if source is RiderPass
        {
            var pass := source as RiderPass;
            var ID := pass.Read();
            this.state := Processing;

            if ID < 0 || !HasKDigits(ID, 8)
            {
                this.state := Closed;
                res := false;
                print "Error in ID", "\n";
                return;
            }

            var passRides := pass.GetRides();
            if passRides <= 0
            {
                this.state := Closed;
                res := false;
                print "Low On Rides", "\n";
                return;
            }

            pass.ConsumeRide();
            this.state := Closed;
            DoorCycle(tickCount, PersonTick);
            res := true;
            return;

        }
        else if source is PaymentCard
        {
            var card := source as PaymentCard;
            var ID := card.Read();
            this.state := Processing;

            if ID < 0 || !HasKDigits(ID, 16)
            {
                this.state := Closed;
                res := false;
                print "Error in ID", "\n";
                return;
            }

            var check := LuhnCheck(ID);

            if !check
            {
                this.state := Closed;
                res := false;
                print "Failed Luhn Check", "\n";
                return;
            }

            var cardBal := card.GetBal();
            if cardBal <= 0.0 || cardBal <= bill
            {
                this.state := Closed;
                res := false;
                print "Low Balance", "\n";
                return;
            }

            card.Deduct(bill);

            this.state := Closed;
            DoorCycle(tickCount, PersonTick);
            res := true;
            return;
        }

        res := false;
        return;
    }

    method DoorCycle(ticks : int, personAtTick : int)
        requires Valid()
        modifies this
        ensures Valid()

        requires 0 <= personAtTick < ticks

        requires state == Closed
        ensures state == Closed
        ensures bill == old(bill)
    {
        OpenTurner(ticks);

        var i := 0;
        while i < ticks && state == Open
            invariant Valid()
            invariant state == Open || state == Closed
            invariant personPassed ==> state == Closed
            invariant !personPassed ==> timerTicks == ticks - i
            invariant timerTicks == 0 ==> state == Closed
            invariant 0 <= timerTicks
            invariant bill == old(bill)
            decreases ticks - i 
        {
            if i == personAtTick && 0 < personAtTick
            {
                PersonPassed();
            }
            else
            {
                Tick();
            }
            i := i + 1;
        }
        print "Turner closed at: ", i - 1, "\n";
    }

    method OpenTurner(ticks : int)
        requires Valid()
        modifies this
        ensures Valid()

        requires 0 < ticks 
        requires state == Closed
        ensures state == Open
        ensures 0 < timerTicks && timerTicks == ticks
        ensures personPassed == false
        ensures bill == old(bill)
    {
        state := Open;
        gate := true;
        timerTicks := ticks;
        personPassed := false;
        print "Turner opened", "\n";
    }

    method PersonPassed()
        requires Valid()
        modifies this 
        ensures Valid()

        requires state == Open
        ensures personPassed == true
        ensures state == Closed
        ensures timerTicks == 0
        ensures bill == old(bill)
    {
        state := Closed;
        gate := false;
        timerTicks := 0;
        personPassed := true;
        print "Person passed", "\n";
    }

    method Tick()
        requires Valid()
        modifies this
        ensures Valid()

        requires state == Open
        ensures timerTicks == old(timerTicks) - 1
        ensures 0 < timerTicks ==> state == Open
        ensures timerTicks == 0 ==> state == Closed
        ensures personPassed == old(personPassed)
        ensures bill == old(bill)
    {
        timerTicks := timerTicks - 1;
        if timerTicks == 0
        {
            state := Closed;
            gate := false;
        }

    }

    method LuhnCheck(ID : int) returns (res : bool)
        requires Valid()
        ensures Valid()

        requires 0 <= ID
        requires HasKDigits(ID, 16)
    {
        var digits : seq<int> := [];

        var n := ID;
        while 0 < n
            decreases n
        {
            digits := [n % 10] + digits;
            n := n / 10;
        }

        var digSum := 0;
        var even := false;
        var i := |digits| - 1;

        while 0 <= i
            decreases i
        {
            var d := digits[i];

            if even
            {
                d := d * 2;
                if d > 9
                {
                    d := d - 9;
                }
            }

            digSum := digSum + d;
            even := !even;
            i := i - 1;
        }

        res := digSum % 10 == 0;
    }

    function HasKDigits(n: int, k: int): bool
        requires n >= 0
        requires k >= 1
    {
        var lower := Pow10(k - 1);
        var upper := Pow10(k);
        lower <= n < upper
    }

    function Pow10(exp: int): int
        requires exp >= 0
        decreases exp
    {
        if exp == 0 then 1
        else 10 * Pow10(exp - 1)
    }
}