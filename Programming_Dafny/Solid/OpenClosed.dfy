trait PaymentProcessor
{
    method ProcessPayment(amount : real) returns (result : bool)
    {
        print amount, " got default processed ", "\n";
        result := true;
    }
}

class DefaultImplementation extends PaymentProcessor
{

}

class CreditCardProcessor extends PaymentProcessor
{
    method ProcessPayment(amount : real) returns (result : bool)
    {
        print amount, " on credit card got processed ", "\n";
        result := true;
    }
}

class VenmoProcessor extends PaymentProcessor
{
    method ProcessPayment(amount : real) returns (result : bool)
    {
        print amount, " on Venmo got processed ", "\n";
        result := true;
    }
}

method Process(obj : PaymentProcessor, amount : real)
{
    var result := obj.ProcessPayment(amount);
    print "Result was: ", result, "\n";
}

method Main()
{
    var df := new DefaultImplementation;
    var card := new CreditCardProcessor;
    var venmo := new VenmoProcessor;

    Process(df, 10.0);
    Process(card, 15.0);
    Process(venmo, 0.99);
}