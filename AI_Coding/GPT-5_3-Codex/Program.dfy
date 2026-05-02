//include "Turnstile.dfy"

method Main()
{
  var turnstile := new Turnstile(3);

  var validCard := new PaymentCard("4532015112830366", 10);
  var cardSource := PaymentSource(validCard);
  var cardOpened := turnstile.ProcessSource(cardSource, true, 5);
  assert cardOpened;
  assert validCard.balance == 7;
  assert turnstile.state == Closed;
  assert !turnstile.tripodOpen;

  var invalidCard := new PaymentCard("1234567890123456", 10);
  var invalidCardSource := PaymentSource(invalidCard);
  var invalidOpened := turnstile.ProcessSource(invalidCardSource, false, 4);
  assert !invalidOpened;
  assert invalidCard.balance == 10;
  assert turnstile.state == Closed;

  var pass := new RiderPass("12345678", 1);
  var passSource := PassSource(pass);
  var passOpened := turnstile.ProcessSource(passSource, false, 2);
  assert passOpened;
  assert pass.rides == 0;
  assert turnstile.state == Closed;

  var emptyPass := new RiderPass("87654321", 0);
  var emptyPassSource := PassSource(emptyPass);
  var emptyPassOpened := turnstile.ProcessSource(emptyPassSource, false, 2);
  assert !emptyPassOpened;
  assert emptyPass.rides == 0;

  var unknown := UnknownSource;
  var unknownOpened := turnstile.ProcessSource(unknown, false, 3);
  assert !unknownOpened;
  assert turnstile.state == Closed;
  assert !turnstile.tripodOpen;
}