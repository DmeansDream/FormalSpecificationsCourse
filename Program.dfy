include "CardClasses.dfy"
include "Turnstile.dfy"

method Main()
{
    var turnstile := new Turnstile(Boot, 20.0); 
    var pass := new RiderPass(88884444, 0);
    var card := new PaymentCard(4444_3333_2222_1111, 50.0);

    var falseCard := new PaymentCard(5089_6897_8238_9771, 50.0); 

    turnstile.Initialize();

    var test := turnstile.ProcessNFCSource(falseCard);

    expect test == false;

    var res1 := turnstile.ProcessNFCSource(pass);
    print "Operation completed?: ", res1, "\n";
    assert res1 ==> pass.rides == 0;

    var res2 := turnstile.ProcessNFCSource(pass);
    print "Operation completed?: ", res2, "\n";
    assert res1 && res2 ==> pass.rides == 0; 

    var res3 := turnstile.ProcessNFCSource(pass);
    print "Operation completed?: ", res3, "\n";
    assert res1 && res2 ==> !res3;

    var res4 := turnstile.ProcessNFCSource(card);
    print "Operation completed?: ", res4, "\n";
    assert res4 ==> card.balance == 30.0;

    var res5 := turnstile.ProcessNFCSource(card);
    print "Operation completed?: ", res5, "\n";
    assert res4 && res5 ==> card.balance == 10.0;

    var res6 := turnstile.ProcessNFCSource(card);
    print "Operation completed?: ", res6, "\n";
    assert res4 && res5 && !res6 ==> card.balance == 10.0;
}