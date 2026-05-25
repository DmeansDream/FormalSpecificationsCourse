// Dafny program Program.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in .NET should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Collections;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// dafny 4.11.0.0
// Command-line arguments: translate --target cs --verification-time-limit 360 --output ./Solution/GPTTranslate Program.dfy
// Program.dfy

method Main(_noArgsParameter: seq<seq<char>>)
{
  var turnstile := new Turnstile(3);
  var validCard := new PaymentCard(""4532015112830366"", 10);
  var isValid := validCard.Valid();
  var isEnoughBal := validCard.balance == 10;
  var cardSource := PaymentSource(validCard);
  var cardOpened := turnstile.ProcessSource(cardSource, true, 5);
  assert isValid ==> cardOpened == true;
  assert isValid && isEnoughBal ==> validCard.balance == 7;
  assert turnstile.state == Closed;
  assert !turnstile.tripodOpen;
  var invalidCard := new PaymentCard(""1234567890123456"", 10);
  var isInvalid := invalidCard.Valid();
  var invalidCardSource := PaymentSource(invalidCard);
  var invalidOpened := turnstile.ProcessSource(invalidCardSource, false, 4);
  assert !isInvalid ==> invalidOpened == false;
  assert !isInvalid ==> invalidCard.balance == 10;
  assert !isInvalid ==> turnstile.state == Closed;
  var pass := new RiderPass(""12345678"", 1);
  var isValPass := pass.Valid();
  var passSource := PassSource(pass);
  var passOpened := turnstile.ProcessSource(passSource, false, 2);
  assert isValPass ==> passOpened;
  assert isValPass ==> pass.rides == 0;
  assert isValPass ==> turnstile.state == Closed;
  var emptyPass := new RiderPass(""87654321"", 0);
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

predicate IsDigit(c: char)
  decreases c
{
  '0' <= c <= '9'
}

function DigitValue(c: char): nat
  decreases c
{
  if IsDigit(c) then
    (c as int - '0' as int) as nat
  else
    0
}

predicate DigitsOnly(s: string)
  decreases |s|
{
  |s| == 0 || (IsDigit(s[0]) && DigitsOnly(s[1..]))
}

function LuhnDouble(d: nat): nat
  decreases d
{
  if d * 2 > 9 then
    d * 2 - 9
  else
    d * 2
}

function LuhnSumFromLeft(s: string, idx: nat): nat
  requires DigitsOnly(s)
  requires idx <= |s|
  decreases |s| - idx
{
  if idx == |s| then
    0
  else
    var d: nat := DigitValue(s[idx]); var distanceFromRight: int := |s| - idx; (if distanceFromRight % 2 == 0 then LuhnDouble(d) else d) + LuhnSumFromLeft(s, idx + 1)
}

predicate IsValidPaymentNumber(s: string)
  decreases s
{
  |s| == 16 &&
  DigitsOnly(s) &&
  LuhnSumFromLeft(s, 0) % 10 == 0
}

predicate IsValidPassId(s: string)
  decreases s
{
  |s| == 8 &&
  DigitsOnly(s)
}

datatype TurnstileState = Open | Closed

class Turnstile {
  const fare: nat
  var state: TurnstileState
  var tripodOpen: bool
  var openTicksRemaining: nat

  predicate StateConsistent()
    reads this
    decreases {this}
  {
    fare > 0 &&
    (tripodOpen <==> state == Open) &&
    (state == Open ==>
      openTicksRemaining > 0) &&
    (state == Closed ==>
      openTicksRemaining == 0)
  }

  constructor (initialFare: nat)
    requires initialFare > 0
    ensures fare == initialFare
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures StateConsistent()
    decreases initialFare
  {
    fare := initialFare;
    state := Closed;
    tripodOpen := false;
    openTicksRemaining := 0;
  }

  function SourceObjects(src: NfcSource): set<object>
    decreases src
  {
    match src
    case PaymentSource(card) =>
      {card}
    case PassSource(pass) =>
      {pass}
    case UnknownSource() =>
      {}
  }

  method AttemptTransaction(src: NfcSource) returns (success: bool)
    requires StateConsistent()
    modifies SourceObjects(src)
    ensures StateConsistent()
    ensures match src case PaymentSource(card) => success <==> old(card.Valid()) && old(card.balance) >= fare case PassSource(pass) => success <==> old(pass.Valid()) && old(pass.rides) > 0 case UnknownSource() => !success
    ensures match src case PaymentSource(card) => !success ==> card.balance == old(card.balance) case PassSource(pass) => !success ==> pass.rides == old(pass.rides) case UnknownSource() => true
    ensures match src case PaymentSource(card) => success ==> card.balance + fare == old(card.balance) case PassSource(pass) => success ==> pass.rides + 1 == old(pass.rides) case UnknownSource() => true
    decreases src
  {
    match src
    case {:split false} PaymentSource(card) =>
      success := card.TryCharge(fare);
    case {:split false} PassSource(pass) =>
      success := pass.TryUseRide();
    case {:split false} UnknownSource() =>
      success := false;
  }

  method Close()
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
  {
    state := Closed;
    tripodOpen := false;
    openTicksRemaining := 0;
  }

  method OpenForTicks(ticks: nat)
    requires ticks > 0
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures state == Open
    ensures tripodOpen
    ensures openTicksRemaining == ticks
    decreases ticks
  {
    state := Open;
    tripodOpen := true;
    openTicksRemaining := ticks;
  }

  method PassengerPassed()
    requires state == Open
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
  {
    Close();
  }

  method Tick()
    requires StateConsistent()
    modifies this
    ensures StateConsistent()
    ensures old(state) == Closed ==> state == Closed
    ensures old(state) == Open ==> state == Closed || openTicksRemaining < old(openTicksRemaining)
  {
    if state == Open {
      if openTicksRemaining > 1 {
        openTicksRemaining := openTicksRemaining - 1;
      } else {
        Close();
      }
    }
  }

  method ProcessSource(src: NfcSource, passengerWalked: bool, timeoutTicks: nat)
      returns (result: bool)
    requires timeoutTicks > 0
    requires StateConsistent()
    modifies this, SourceObjects(src)
    ensures StateConsistent()
    ensures state == Closed
    ensures !tripodOpen
    ensures openTicksRemaining == 0
    ensures match src case PaymentSource(card) => result <==> old(card.Valid()) && old(card.balance) >= fare case PassSource(pass) => result <==> old(pass.Valid()) && old(pass.rides) > 0 case UnknownSource() => !result
    ensures match src case PaymentSource(card) => !result ==> card.balance == old(card.balance) case PassSource(pass) => !result ==> pass.rides == old(pass.rides) case UnknownSource() => true
    ensures match src case PaymentSource(card) => result ==> card.balance + fare == old(card.balance) case PassSource(pass) => result ==> pass.rides + 1 == old(pass.rides) case UnknownSource() => true
    decreases src, passengerWalked, timeoutTicks
  {
    match src
    case {:split false} PaymentSource(card) =>
      var valid0 := card.Valid();
      var bal0 := card.balance;
      result := AttemptTransaction(src);
      assert result <==> valid0 && bal0 >= fare;
      if result {
        assert card.balance + fare == bal0;
        OpenForTicks(timeoutTicks);
        if passengerWalked {
          PassengerPassed();
        } else {
          while state == Open
            invariant StateConsistent()
            decreases openTicksRemaining
            modifies this
          {
            Tick();
          }
        }
      } else {
        assert card.balance == bal0;
        Close();
      }
      if result {
        assert card.balance + fare == bal0;
      } else {
        assert card.balance == bal0;
      }
    case {:split false} PassSource(pass) =>
      var valid0 := pass.Valid();
      var rides0 := pass.rides;
      result := AttemptTransaction(src);
      assert result <==> valid0 && rides0 > 0;
      if result {
        assert pass.rides + 1 == rides0;
        OpenForTicks(timeoutTicks);
        if passengerWalked {
          PassengerPassed();
        } else {
          while state == Open
            invariant StateConsistent()
            decreases openTicksRemaining
            modifies this
          {
            Tick();
          }
        }
      } else {
        assert pass.rides == rides0;
        Close();
      }
      if result {
        assert pass.rides + 1 == rides0;
      } else {
        assert pass.rides == rides0;
      }
    case {:split false} UnknownSource() =>
      result := AttemptTransaction(src);
      assert !result;
      Close();
  }
}

class RiderPass {
  var id: string
  var rides: nat

  predicate Valid()
    reads this
    decreases {this}
  {
    IsValidPassId(id)
  }

  constructor (passId: string, initialRides: nat)
    ensures id == passId
    ensures rides == initialRides
    decreases passId, initialRides
  {
    id := passId;
    rides := initialRides;
  }

  method TryUseRide() returns (ok: bool)
    modifies this
    ensures rides >= 0
    ensures ok <==> old(Valid()) && old(rides) > 0
    ensures ok ==> rides + 1 == old(rides)
    ensures !ok ==> rides == old(rides)
  {
    if Valid() && rides > 0 {
      rides := rides - 1;
      ok := true;
    } else {
      ok := false;
    }
  }
}

class PaymentCard {
  var number: string
  var balance: nat

  predicate Valid()
    reads this
    decreases {this}
  {
    IsValidPaymentNumber(number)
  }

  constructor (cardNumber: string, initialBalance: nat)
    ensures number == cardNumber
    ensures balance == initialBalance
    decreases cardNumber, initialBalance
  {
    number := cardNumber;
    balance := initialBalance;
  }

  method TryCharge(amount: nat) returns (ok: bool)
    requires amount > 0
    modifies this
    ensures balance >= 0
    ensures ok <==> old(Valid()) && old(balance) >= amount
    ensures ok ==> balance + amount == old(balance)
    ensures !ok ==> balance == old(balance)
    decreases amount
  {
    if Valid() && balance >= amount {
      balance := balance - amount;
      ok := true;
    } else {
      ok := false;
    }
  }
}

datatype NfcSource = PaymentSource(card: PaymentCard) | PassSource(pass: RiderPass) | UnknownSource
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
internal static class FuncExtensions {
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
}
// end of class FuncExtensions
namespace _module {

  public partial class __default {
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      Turnstile _0_turnstile;
      Turnstile _nw0 = new Turnstile();
      _nw0.__ctor(new BigInteger(3));
      _0_turnstile = _nw0;
      PaymentCard _1_validCard;
      PaymentCard _nw1 = new PaymentCard();
      _nw1.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("4532015112830366"), new BigInteger(10));
      _1_validCard = _nw1;
      bool _2_isValid;
      _2_isValid = (_1_validCard).Valid();
      bool _3_isEnoughBal;
      _3_isEnoughBal = (_1_validCard.balance) == (new BigInteger(10));
      _INfcSource _4_cardSource;
      _4_cardSource = _module.NfcSource.create_PaymentSource(_1_validCard);
      bool _5_cardOpened;
      bool _out0;
      _out0 = (_0_turnstile).ProcessSource(_4_cardSource, true, new BigInteger(5));
      _5_cardOpened = _out0;
      PaymentCard _6_invalidCard;
      PaymentCard _nw2 = new PaymentCard();
      _nw2.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("1234567890123456"), new BigInteger(10));
      _6_invalidCard = _nw2;
      bool _7_isInvalid;
      _7_isInvalid = (_6_invalidCard).Valid();
      _INfcSource _8_invalidCardSource;
      _8_invalidCardSource = _module.NfcSource.create_PaymentSource(_6_invalidCard);
      bool _9_invalidOpened;
      bool _out1;
      _out1 = (_0_turnstile).ProcessSource(_8_invalidCardSource, false, new BigInteger(4));
      _9_invalidOpened = _out1;
      RiderPass _10_pass;
      RiderPass _nw3 = new RiderPass();
      _nw3.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("12345678"), BigInteger.One);
      _10_pass = _nw3;
      bool _11_isValPass;
      _11_isValPass = (_10_pass).Valid();
      _INfcSource _12_passSource;
      _12_passSource = _module.NfcSource.create_PassSource(_10_pass);
      bool _13_passOpened;
      bool _out2;
      _out2 = (_0_turnstile).ProcessSource(_12_passSource, false, new BigInteger(2));
      _13_passOpened = _out2;
      RiderPass _14_emptyPass;
      RiderPass _nw4 = new RiderPass();
      _nw4.__ctor(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("87654321"), BigInteger.Zero);
      _14_emptyPass = _nw4;
      bool _15_isEmptyPass;
      _15_isEmptyPass = (_14_emptyPass).Valid();
      _INfcSource _16_emptyPassSource;
      _16_emptyPassSource = _module.NfcSource.create_PassSource(_14_emptyPass);
      bool _17_emptyPassOpened;
      bool _out3;
      _out3 = (_0_turnstile).ProcessSource(_16_emptyPassSource, false, new BigInteger(2));
      _17_emptyPassOpened = _out3;
      _INfcSource _18_unknown;
      _18_unknown = _module.NfcSource.create_UnknownSource();
      bool _19_unknownOpened;
      bool _out4;
      _out4 = (_0_turnstile).ProcessSource(_18_unknown, false, new BigInteger(3));
      _19_unknownOpened = _out4;
    }
    public static bool IsDigit(Dafny.Rune c) {
      return ((new Dafny.Rune('0')) <= (c)) && ((c) <= (new Dafny.Rune('9')));
    }
    public static BigInteger DigitValue(Dafny.Rune c) {
      if (__default.IsDigit(c)) {
        return (new BigInteger((c).Value)) - (new BigInteger((new Dafny.Rune('0')).Value));
      } else {
        return BigInteger.Zero;
      }
    }
    public static bool DigitsOnly(Dafny.ISequence<Dafny.Rune> s) {
      return ((new BigInteger((s).Count)).Sign == 0) || ((__default.IsDigit((s).Select(BigInteger.Zero))) && (__default.DigitsOnly((s).Drop(BigInteger.One))));
    }
    public static BigInteger LuhnDouble(BigInteger d) {
      if (((d) * (new BigInteger(2))) > (new BigInteger(9))) {
        return ((d) * (new BigInteger(2))) - (new BigInteger(9));
      } else {
        return (d) * (new BigInteger(2));
      }
    }
    public static BigInteger LuhnSumFromLeft(Dafny.ISequence<Dafny.Rune> s, BigInteger idx)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((idx) == (new BigInteger((s).Count))) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        BigInteger _1_d = __default.DigitValue((s).Select(idx));
        BigInteger _2_distanceFromRight = (new BigInteger((s).Count)) - (idx);
        _0___accumulator = (_0___accumulator) + ((((Dafny.Helpers.EuclideanModulus(_2_distanceFromRight, new BigInteger(2))).Sign == 0) ? (__default.LuhnDouble(_1_d)) : (_1_d)));
        Dafny.ISequence<Dafny.Rune> _in0 = s;
        BigInteger _in1 = (idx) + (BigInteger.One);
        s = _in0;
        idx = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool IsValidPaymentNumber(Dafny.ISequence<Dafny.Rune> s) {
      return (((new BigInteger((s).Count)) == (new BigInteger(16))) && (__default.DigitsOnly(s))) && ((Dafny.Helpers.EuclideanModulus(__default.LuhnSumFromLeft(s, BigInteger.Zero), new BigInteger(10))).Sign == 0);
    }
    public static bool IsValidPassId(Dafny.ISequence<Dafny.Rune> s) {
      return ((new BigInteger((s).Count)) == (new BigInteger(8))) && (__default.DigitsOnly(s));
    }
  }

  public interface _ITurnstileState {
    bool is_Open { get; }
    bool is_Closed { get; }
    _ITurnstileState DowncastClone();
  }
  public abstract class TurnstileState : _ITurnstileState {
    public TurnstileState() {
    }
    private static readonly _ITurnstileState theDefault = create_Open();
    public static _ITurnstileState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_ITurnstileState> _TYPE = new Dafny.TypeDescriptor<_ITurnstileState>(TurnstileState.Default());
    public static Dafny.TypeDescriptor<_ITurnstileState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITurnstileState create_Open() {
      return new TurnstileState_Open();
    }
    public static _ITurnstileState create_Closed() {
      return new TurnstileState_Closed();
    }
    public bool is_Open { get { return this is TurnstileState_Open; } }
    public bool is_Closed { get { return this is TurnstileState_Closed; } }
    public static System.Collections.Generic.IEnumerable<_ITurnstileState> AllSingletonConstructors {
      get {
        yield return TurnstileState.create_Open();
        yield return TurnstileState.create_Closed();
      }
    }
    public abstract _ITurnstileState DowncastClone();
  }
  public class TurnstileState_Open : TurnstileState {
    public TurnstileState_Open() : base() {
    }
    public override _ITurnstileState DowncastClone() {
      if (this is _ITurnstileState dt) { return dt; }
      return new TurnstileState_Open();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileState_Open;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileState.Open";
      return s;
    }
  }
  public class TurnstileState_Closed : TurnstileState {
    public TurnstileState_Closed() : base() {
    }
    public override _ITurnstileState DowncastClone() {
      if (this is _ITurnstileState dt) { return dt; }
      return new TurnstileState_Closed();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileState_Closed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileState.Closed";
      return s;
    }
  }

  public partial class Turnstile {
    public Turnstile() {
      this.state = TurnstileState.Default();
      this.tripodOpen = false;
      this.openTicksRemaining = BigInteger.Zero;
      this._fare = BigInteger.Zero;
    }
    public _ITurnstileState state {get; set;}
    public bool tripodOpen {get; set;}
    public BigInteger openTicksRemaining {get; set;}
    public bool StateConsistent() {
      return (((((this).fare).Sign == 1) && ((this.tripodOpen) == (object.Equals(this.state, _module.TurnstileState.create_Open())))) && (!(object.Equals(this.state, _module.TurnstileState.create_Open())) || ((this.openTicksRemaining).Sign == 1))) && (!(object.Equals(this.state, _module.TurnstileState.create_Closed())) || ((this.openTicksRemaining).Sign == 0));
    }
    public void __ctor(BigInteger initialFare)
    {
      (this)._fare = initialFare;
      (this).state = _module.TurnstileState.create_Closed();
      (this).tripodOpen = false;
      (this).openTicksRemaining = BigInteger.Zero;
    }
    public Dafny.ISet<object> SourceObjects(_INfcSource src) {
      _INfcSource _source0 = src;
      {
        if (_source0.is_PaymentSource) {
          PaymentCard _0_card = _source0.dtor_card;
          return Dafny.Set<PaymentCard>.FromElements(_0_card);
        }
      }
      {
        if (_source0.is_PassSource) {
          RiderPass _1_pass = _source0.dtor_pass;
          return Dafny.Set<RiderPass>.FromElements(_1_pass);
        }
      }
      {
        return Dafny.Set<object>.FromElements();
      }
    }
    public bool AttemptTransaction(_INfcSource src)
    {
      bool success = false;
      _INfcSource _source0 = src;
      {
        if (_source0.is_PaymentSource) {
          PaymentCard _0_card = _source0.dtor_card;
          bool _out0;
          _out0 = (_0_card).TryCharge((this).fare);
          success = _out0;
          goto after_match0;
        }
      }
      {
        if (_source0.is_PassSource) {
          RiderPass _1_pass = _source0.dtor_pass;
          bool _out1;
          _out1 = (_1_pass).TryUseRide();
          success = _out1;
          goto after_match0;
        }
      }
      {
        success = false;
      }
    after_match0: ;
      return success;
    }
    public void Close()
    {
      (this).state = _module.TurnstileState.create_Closed();
      (this).tripodOpen = false;
      (this).openTicksRemaining = BigInteger.Zero;
    }
    public void OpenForTicks(BigInteger ticks)
    {
      (this).state = _module.TurnstileState.create_Open();
      (this).tripodOpen = true;
      (this).openTicksRemaining = ticks;
    }
    public void PassengerPassed()
    {
      (this).Close();
    }
    public void Tick()
    {
      if (object.Equals(this.state, _module.TurnstileState.create_Open())) {
        if ((this.openTicksRemaining) > (BigInteger.One)) {
          (this).openTicksRemaining = (this.openTicksRemaining) - (BigInteger.One);
        } else {
          (this).Close();
        }
      }
    }
    public bool ProcessSource(_INfcSource src, bool passengerWalked, BigInteger timeoutTicks)
    {
      bool result = false;
      _INfcSource _source0 = src;
      {
        if (_source0.is_PaymentSource) {
          PaymentCard _0_card = _source0.dtor_card;
          bool _1_valid0;
          _1_valid0 = (_0_card).Valid();
          BigInteger _2_bal0;
          _2_bal0 = _0_card.balance;
          bool _out0;
          _out0 = (this).AttemptTransaction(src);
          result = _out0;
          if (result) {
            (this).OpenForTicks(timeoutTicks);
            if (passengerWalked) {
              (this).PassengerPassed();
            } else {
              while (object.Equals(this.state, _module.TurnstileState.create_Open())) {
                (this).Tick();
              }
            }
          } else {
            (this).Close();
          }
          goto after_match0;
        }
      }
      {
        if (_source0.is_PassSource) {
          RiderPass _3_pass = _source0.dtor_pass;
          bool _4_valid0;
          _4_valid0 = (_3_pass).Valid();
          BigInteger _5_rides0;
          _5_rides0 = _3_pass.rides;
          bool _out1;
          _out1 = (this).AttemptTransaction(src);
          result = _out1;
          if (result) {
            (this).OpenForTicks(timeoutTicks);
            if (passengerWalked) {
              (this).PassengerPassed();
            } else {
              while (object.Equals(this.state, _module.TurnstileState.create_Open())) {
                (this).Tick();
              }
            }
          } else {
            (this).Close();
          }
          goto after_match0;
        }
      }
      {
        bool _out2;
        _out2 = (this).AttemptTransaction(src);
        result = _out2;
        (this).Close();
      }
    after_match0: ;
      return result;
    }
    public BigInteger _fare {get; set;}
    public BigInteger fare { get {
      return this._fare;
    } }
  }

  public partial class RiderPass {
    public RiderPass() {
      this.id = Dafny.Sequence<Dafny.Rune>.Empty;
      this.rides = BigInteger.Zero;
    }
    public Dafny.ISequence<Dafny.Rune> id {get; set;}
    public BigInteger rides {get; set;}
    public bool Valid() {
      return __default.IsValidPassId(this.id);
    }
    public void __ctor(Dafny.ISequence<Dafny.Rune> passId, BigInteger initialRides)
    {
      (this).id = passId;
      (this).rides = initialRides;
    }
    public bool TryUseRide()
    {
      bool ok = false;
      if (((this).Valid()) && ((this.rides).Sign == 1)) {
        (this).rides = (this.rides) - (BigInteger.One);
        ok = true;
      } else {
        ok = false;
      }
      return ok;
    }
  }

  public partial class PaymentCard {
    public PaymentCard() {
      this.number = Dafny.Sequence<Dafny.Rune>.Empty;
      this.balance = BigInteger.Zero;
    }
    public Dafny.ISequence<Dafny.Rune> number {get; set;}
    public BigInteger balance {get; set;}
    public bool Valid() {
      return __default.IsValidPaymentNumber(this.number);
    }
    public void __ctor(Dafny.ISequence<Dafny.Rune> cardNumber, BigInteger initialBalance)
    {
      (this).number = cardNumber;
      (this).balance = initialBalance;
    }
    public bool TryCharge(BigInteger amount)
    {
      bool ok = false;
      if (((this).Valid()) && ((this.balance) >= (amount))) {
        (this).balance = (this.balance) - (amount);
        ok = true;
      } else {
        ok = false;
      }
      return ok;
    }
  }

  public interface _INfcSource {
    bool is_PaymentSource { get; }
    bool is_PassSource { get; }
    bool is_UnknownSource { get; }
    PaymentCard dtor_card { get; }
    RiderPass dtor_pass { get; }
    _INfcSource DowncastClone();
  }
  public abstract class NfcSource : _INfcSource {
    public NfcSource() {
    }
    private static readonly _INfcSource theDefault = create_PaymentSource(default(PaymentCard));
    public static _INfcSource Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_INfcSource> _TYPE = new Dafny.TypeDescriptor<_INfcSource>(NfcSource.Default());
    public static Dafny.TypeDescriptor<_INfcSource> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INfcSource create_PaymentSource(PaymentCard card) {
      return new NfcSource_PaymentSource(card);
    }
    public static _INfcSource create_PassSource(RiderPass pass) {
      return new NfcSource_PassSource(pass);
    }
    public static _INfcSource create_UnknownSource() {
      return new NfcSource_UnknownSource();
    }
    public bool is_PaymentSource { get { return this is NfcSource_PaymentSource; } }
    public bool is_PassSource { get { return this is NfcSource_PassSource; } }
    public bool is_UnknownSource { get { return this is NfcSource_UnknownSource; } }
    public PaymentCard dtor_card {
      get {
        var d = this;
        return ((NfcSource_PaymentSource)d)._card;
      }
    }
    public RiderPass dtor_pass {
      get {
        var d = this;
        return ((NfcSource_PassSource)d)._pass;
      }
    }
    public abstract _INfcSource DowncastClone();
  }
  public class NfcSource_PaymentSource : NfcSource {
    public readonly PaymentCard _card;
    public NfcSource_PaymentSource(PaymentCard card) : base() {
      this._card = card;
    }
    public override _INfcSource DowncastClone() {
      if (this is _INfcSource dt) { return dt; }
      return new NfcSource_PaymentSource(_card);
    }
    public override bool Equals(object other) {
      var oth = other as NfcSource_PaymentSource;
      return oth != null && this._card == oth._card;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._card));
      return (int) hash;
    }
    public override string ToString() {
      string s = "NfcSource.PaymentSource";
      s += "(";
      s += Dafny.Helpers.ToString(this._card);
      s += ")";
      return s;
    }
  }
  public class NfcSource_PassSource : NfcSource {
    public readonly RiderPass _pass;
    public NfcSource_PassSource(RiderPass pass) : base() {
      this._pass = pass;
    }
    public override _INfcSource DowncastClone() {
      if (this is _INfcSource dt) { return dt; }
      return new NfcSource_PassSource(_pass);
    }
    public override bool Equals(object other) {
      var oth = other as NfcSource_PassSource;
      return oth != null && this._pass == oth._pass;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._pass));
      return (int) hash;
    }
    public override string ToString() {
      string s = "NfcSource.PassSource";
      s += "(";
      s += Dafny.Helpers.ToString(this._pass);
      s += ")";
      return s;
    }
  }
  public class NfcSource_UnknownSource : NfcSource {
    public NfcSource_UnknownSource() : base() {
    }
    public override _INfcSource DowncastClone() {
      if (this is _INfcSource dt) { return dt; }
      return new NfcSource_UnknownSource();
    }
    public override bool Equals(object other) {
      var oth = other as NfcSource_UnknownSource;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "NfcSource.UnknownSource";
      return s;
    }
  }
} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => _module.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
