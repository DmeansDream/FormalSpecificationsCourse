include "Turnstile.dfy"

method Main()
{
  var turnstile := new Turnstile(3);

  var validCard := new PaymentCard("4532015112830366", 10);

  var isValid := validCard.Valid();
  var isEnoughBal := validCard.balance == 10;

  var cardSource := PaymentSource(validCard);
  var cardOpened := turnstile.ProcessSource(cardSource, true, 5);
  assert isValid ==> cardOpened == true;
  assert isValid && isEnoughBal ==> validCard.balance == 7;
  assert turnstile.state == Closed;
  assert !turnstile.tripodOpen;

  var invalidCard := new PaymentCard("1234567890123456", 10);
  var isInvalid := invalidCard.Valid();

  var invalidCardSource := PaymentSource(invalidCard);
  var invalidOpened := turnstile.ProcessSource(invalidCardSource, false, 4);

  assert !isInvalid ==> invalidOpened == false;
  assert !isInvalid ==> invalidCard.balance == 10;
  assert !isInvalid ==> turnstile.state == Closed;

  var pass := new RiderPass("12345678", 1);
  var isValPass := pass.Valid();

  var passSource := PassSource(pass);
  var passOpened := turnstile.ProcessSource(passSource, false, 2);
  assert isValPass ==> passOpened;
  assert isValPass ==> pass.rides == 0;
  assert isValPass ==> turnstile.state == Closed;

  var emptyPass := new RiderPass("87654321", 0);
  var isEmptyPass := emptyPass.Valid();

  var emptyPassSource := PassSource(emptyPass);
  var emptyPassOpened := turnstile.ProcessSource(emptyPassSource, false, 2);
  assert isEmptyPass ==> !emptyPassOpened;
  assert isEmptyPass ==> emptyPass.rides == 0;

  var unknown := UnknownSource;
  var unknownOpened := turnstile.ProcessSource(unknown, false, 3);
  assert !unknownOpened;
  assert turnstile.state == Closed;
  assert !turnstile.tripodOpen;
}