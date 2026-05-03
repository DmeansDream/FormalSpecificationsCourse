trait ServicePolicy
{
    ghost predicate Valid()
        reads this

    method ComputeServiceCost(amount : real) returns (fee : real)
        requires Valid()
        requires 0.0 <= amount
        ensures 0.0 <= fee <= amount

}

class FlatFeePolicy extends ServicePolicy
{
    const flatFee : real

    ghost predicate Valid()
        reads this
    {
        0.0 <= flatFee
    }

    constructor(f : real)
        requires 0.0 <= f
        ensures flatFee == f
        ensures Valid()
    {
        flatFee := f;
    }

    method ComputeServiceCost(amount : real) returns (fee : real)
        requires Valid()
        requires 0.0 <= amount
        ensures 0.0 <= fee <= amount
    {
        fee := if flatFee <= amount then flatFee else amount;
    }
}

class PercentageFeePolicy extends ServicePolicy
{
    const percentageFee : real

    ghost predicate Valid()
        reads this
    {
        0.0 <= percentageFee < 100.0
    }

    constructor(f : real)
        requires 0.0 <= f < 100.0
        ensures percentageFee == f
        ensures Valid()
    {
        percentageFee := f;
    }

    method ComputeServiceCost(amount : real) returns (fee : real)
        requires Valid()
        requires 0.0 <= amount
        ensures 0.0 <= fee <= amount
    {
        var ratio := percentageFee / 100.0;
        assert 0.0 <= ratio < 1.0;

        fee := amount * ratio;
        if amount > 0.0 {
            assert amount * ratio <= amount * 1.0; 
        }
    }
}

class CardService
{
    const feePolicy : ServicePolicy?

    ghost predicate Valid()
        reads this, feePolicy
    {
        feePolicy != null &&
        feePolicy.Valid()
    }

    constructor(policy : ServicePolicy)
        requires policy.Valid()
        ensures feePolicy == policy
        ensures Valid()
    {
        feePolicy := policy;
    }

    method ProcessPayment(amount : real) returns (netAmount : real, fee : real)
        requires Valid()
        requires 0.0 < amount
        
        ensures 0.0 <= fee
        ensures 0.0 <= netAmount
        ensures netAmount + fee == amount 
        ensures Valid()
    {
        fee := feePolicy.ComputeServiceCost(amount);
        netAmount := amount - fee;
    }
}


method Main()
{
    // flat fee
    var flat := new FlatFeePolicy(0.5);
    var service1 := new CardService(flat);
    var remaining, fee := service1.ProcessPayment(200.0);

    print "Remaining bal: ", remaining, " Fee: ", fee, "\n";

    // percentage fee
    var perc := new PercentageFeePolicy(0.5);
    var service2 := new CardService(perc);
    var remaining2, fee2 := service2.ProcessPayment(200.0);

    print "Remaining bal: ", remaining2, " Fee: ", fee2, "\n";
}