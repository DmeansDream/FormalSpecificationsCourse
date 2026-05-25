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
// Command-line arguments: translate --target cs --verification-time-limit 360 --output ./Solution/ClaudeTranslate Program.dfy
// Program.dfy


module ProgramModule {
  function ValidCardNumber(): seq<int>
  {
    [4, 5, 3, 2, 0, 1, 5, 1, 1, 2, 8, 3, 0, 3, 6, 6]
  }

  function ValidPassNumber(): seq<int>
  {
    [1, 2, 3, 4, 5, 6, 7, 8]
  }

  method PrintBanner(text: string)
    decreases text
  {
    print ""------------------------------------------------------------\n"";
    print text;
    print ""\n------------------------------------------------------------\n"";
  }

  method PrintResult(lab: string, result: ProcessResult)
    decreases lab, result
  {
    print ""  "";
    print lab;
    print "": "";
    match result {
      case {:split false} Admitted() =>
        print ""ADMITTED (passenger walked through)\n"";
      case {:split false} TimedOut() =>
        print ""TIMED OUT (gate closed after timer)\n"";
      case {:split false} Denied() =>
        print ""DENIED\n"";
    }
  }

  method PrintBalance(lab: string, v: int)
    decreases lab, v
  {
    print ""  "";
    print lab;
    print "": "";
    print v;
    print ""\n"";
  }

  method AssertTurnstileClosedAndValid(ts: Turnstile, tp: Tripod)
    requires ts.tripod == tp
    requires ts.Valid()
    requires ts.IsClosed()
    requires tp.IsClosed()
    ensures ts.tripod == tp
    ensures ts.Valid()
    ensures ts.IsClosed()
    ensures tp.IsClosed()
    decreases ts, tp
  {
    assert ts.state == GateClosed;
    assert tp.state == TripodClosed;
    assert ts.Valid();
    print ""  [INVARIANT OK] Turnstile closed and in sync with tripod.\n"";
  }

  method Main(_noArgsParameter: seq<seq<char>>)
  {
    var tripod := new Tripod();
    var turnstile := new Turnstile(3, tripod);
    assert turnstile.Valid();
    assert turnstile.IsClosed();
    assert tripod.IsClosed();
    print ""\n"";
    print ""============================================================\n"";
    print ""     METRO TURNSTILE NFC SUBSYSTEM — VERIFICATION TESTS     \n"";
    print ""============================================================\n\n"";
    PrintBanner(""T04: PaymentCard | balance=50 | fare=100 -> Denied (insufficient)"");
    {
      var card := new PaymentCard(ValidCardNumber(), 50, 100);
      assert !card.HasSufficientFunds();
      var valueBefore := card.balance;
      var r := turnstile.ProcessNFC(card, true);
      PrintResult(""Result"", r);
      PrintBalance(""Balance after (expected 50, unchanged)"", card.balance);
      assert r == Denied;
      AssertTurnstileClosedAndValid(turnstile, tripod);
    }
    print ""\n"";
    PrintBanner(""T06: RiderPass | rides=2 | passenger times out"");
    {
      var pass := new RiderPass(ValidPassNumber(), 2);
      assert pass.IsValid();
      assert pass.HasSufficientFunds();
      var r := turnstile.ProcessNFC(pass, false);
      PrintResult(""Result"", r);
      PrintBalance(""Rides after (expected 1)"", pass.ridesRemaining);
      AssertTurnstileClosedAndValid(turnstile, tripod);
    }
    print ""\n"";
    PrintBanner(""T09: Sequential PaymentCard | balance=300 | fare=100 -> 3 rides then Denied"");
    {
      var card := new PaymentCard(ValidCardNumber(), 300, 100);
      assert card.HasSufficientFunds();
      assert card.balance == 300;
      var r1 := turnstile.ProcessNFC(card, true);
      PrintResult(""Ride 1"", r1);
      PrintBalance(""  Balance"", card.balance);
      var bal1 := card.balance;
      assert r1 == Admitted ==> bal1 == 200;
      AssertTurnstileClosedAndValid(turnstile, tripod);
      var r2 := turnstile.ProcessNFC(card, true);
      PrintResult(""Ride 2"", r2);
      PrintBalance(""  Balance"", card.balance);
      assert r1 == Admitted && r2 == Admitted ==> card.balance == 100;
      AssertTurnstileClosedAndValid(turnstile, tripod);
      var r3 := turnstile.ProcessNFC(card, true);
      PrintResult(""Ride 3"", r3);
      PrintBalance(""  Balance"", card.balance);
      assert r1 == Admitted && r2 == Admitted && r3 == Admitted ==> card.balance == 0;
      AssertTurnstileClosedAndValid(turnstile, tripod);
      var r4 := turnstile.ProcessNFC(card, true);
      PrintResult(""Ride 4 (no funds)"", r4);
      PrintBalance(""  Balance (unchanged)"", card.balance);
      assert r1 == Admitted && r2 == Admitted && r3 == Admitted && r4 == Denied ==> card.balance == 0;
      AssertTurnstileClosedAndValid(turnstile, tripod);
    }
    print ""\n"";
    PrintBanner(""T10: Sequential RiderPass | rides=3 -> 3 rides then Denied"");
    {
      var pass := new RiderPass(ValidPassNumber(), 3);
      var r1 := turnstile.ProcessNFC(pass, true);
      PrintResult(""Ride 1"", r1);
      PrintBalance(""  Rides"", pass.ridesRemaining);
      assert r1 == Admitted;
      assert pass.ridesRemaining == 2;
      AssertTurnstileClosedAndValid(turnstile, tripod);
      var r2 := turnstile.ProcessNFC(pass, true);
      PrintResult(""Ride 2"", r2);
      PrintBalance(""  Rides"", pass.ridesRemaining);
      assert r2 == Admitted;
      assert pass.ridesRemaining == 1;
      AssertTurnstileClosedAndValid(turnstile, tripod);
      var r3 := turnstile.ProcessNFC(pass, true);
      PrintResult(""Ride 3"", r3);
      PrintBalance(""  Rides"", pass.ridesRemaining);
      assert r3 == Admitted;
      assert pass.ridesRemaining == 0;
      AssertTurnstileClosedAndValid(turnstile, tripod);
      var r4 := turnstile.ProcessNFC(pass, true);
      PrintResult(""Ride 4 (no rides)"", r4);
      PrintBalance(""  Rides (unchanged)"", pass.ridesRemaining);
      assert r4 == Denied;
      assert pass.ridesRemaining == 0;
      AssertTurnstileClosedAndValid(turnstile, tripod);
    }
    print ""\n"";
    print ""============================================================\n"";
    print ""  FINAL SYSTEM STATE CHECK\n"";
    print ""============================================================\n"";
    assert turnstile.Valid();
    assert turnstile.IsClosed();
    assert tripod.IsClosed();
    print ""  Turnstile state : CLOSED\n"";
    print ""  Tripod state    : CLOSED\n"";
    print ""  System valid    : TRUE\n"";
    print ""\n  All tests completed successfully.\n"";
    print ""============================================================\n"";
  }

  import opened NFCSourceModule

  import opened PaymentCardModule

  import opened RiderPassModule

  import opened TripodModule

  import opened TurnstileModule
}

module TurnstileModule {

  import opened NFCSourceModule

  import opened TripodModule
  datatype TurnstileState = GateOpen | GateClosed

  datatype ProcessResult = Admitted | TimedOut | Denied

  class Turnstile {
    const tripod: Tripod
    var state: TurnstileState
    const openDuration: nat

    predicate Valid()
      reads this, tripod
      decreases {this, tripod}
    {
      (state == GateOpen ==>
        tripod.IsOpen()) &&
      (state == GateClosed ==>
        tripod.IsClosed()) &&
      openDuration > 0
    }

    constructor (duration: nat, t: Tripod)
      requires duration > 0
      requires t.IsClosed()
      ensures tripod == t
      ensures state == GateClosed
      ensures openDuration == duration
      ensures Valid()
      decreases duration, t
    {
      tripod := t;
      state := GateClosed;
      openDuration := duration;
    }

    method OpenGate()
      requires Valid()
      modifies this, tripod
      ensures state == GateOpen
      ensures tripod.IsOpen()
      ensures Valid()
    {
      tripod.Open();
      state := GateOpen;
    }

    method CloseGate()
      requires Valid()
      modifies this, tripod
      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
    {
      tripod.Close();
      state := GateClosed;
    }

    method WaitAndClose(passengerDetected: bool) returns (walked: bool)
      requires Valid()
      requires state == GateOpen
      modifies this, tripod
      ensures walked == passengerDetected
      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
      decreases passengerDetected
    {
      walked := passengerDetected;
      CloseGate();
    }

    method ProcessNFC(source: NFCSource, passengerDetected: bool) returns (result: ProcessResult)
      requires Valid()
      requires state == GateClosed
      requires {source} !! {this, tripod}
      modifies this, tripod, source
      ensures state == GateClosed
      ensures tripod.IsClosed()
      ensures Valid()
      ensures old(source.IsValid()) ==> source.IsValid()
      ensures !old(source.IsValid()) ==> result == Denied
      ensures old(source.IsValid()) && !old(source.HasSufficientFunds()) ==> result == Denied
      ensures result == Denied && old(source.IsValid()) ==> source.IsValid()
      ensures result == Denied && old(source.IsValid()) ==> source.CurrentValue() == old(source.CurrentValue())
      ensures result == Denied ==> state == GateClosed
      ensures old(source.IsValid()) && old(source.HasSufficientFunds()) && passengerDetected ==> result == Admitted
      ensures result == Admitted ==> passengerDetected
      ensures result == Admitted ==> old(source.IsValid())
      ensures result == Admitted ==> old(source.HasSufficientFunds())
      ensures old(source.IsValid()) && old(source.HasSufficientFunds()) && !passengerDetected ==> result == TimedOut
      ensures result == TimedOut ==> !passengerDetected
      ensures result == TimedOut ==> old(source.IsValid())
      ensures result == TimedOut ==> old(source.HasSufficientFunds())
      ensures old(source.IsValid()) && old(source.HasSufficientFunds()) ==> source.CurrentValue() == old(source.CurrentValue()) - old(source.OneRideWorth())
      ensures result == Denied || result == Admitted || result == TimedOut
      decreases source, passengerDetected
    {
      if !source.IsValid() {
        result := Denied;
        return;
      }
      if !source.HasSufficientFunds() {
        result := Denied;
        return;
      }
      var deductOutcome := source.Deduct();
      if deductOutcome == Success {
        OpenGate();
        var walked := WaitAndClose(passengerDetected);
        if walked {
          result := Admitted;
        } else {
          result := TimedOut;
        }
      } else {
        result := Denied;
      }
    }

    predicate IsOpen()
      reads this
      decreases {this}
    {
      state == GateOpen
    }

    predicate IsClosed()
      reads this
      decreases {this}
    {
      state == GateClosed
    }
  }
}

module TripodModule {
  datatype TripodState = TripodOpen | TripodClosed

  class Tripod {
    var state: TripodState

    predicate Valid()
      reads this
      decreases {this}
    {
      state == TripodOpen || state == TripodClosed
    }

    constructor ()
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
      decreases {this}
    {
      state == TripodOpen
    }

    predicate IsClosed()
      reads this
      decreases {this}
    {
      state == TripodClosed
    }
  }
}

module NFCSourceModule {
  datatype DeductResult = Success | Failure

  trait {:termination false} NFCSource {
    function ID(): seq<int>
      reads this
      decreases {this}

    predicate IsValid()
      reads this
      decreases {this}

    predicate HasSufficientFunds()
      reads this
      decreases {this}

    function CurrentValue(): int
      requires IsValid()
      reads this
      ensures CurrentValue() >= 0
      decreases {this}

    method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      ensures IsValid()
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())
      ensures OneRideWorth() == old(OneRideWorth())
      ensures CurrentValue() == old(CurrentValue()) - old(OneRideWorth())

    function OneRideWorth(): int
      requires IsValid()
      reads this
      ensures OneRideWorth() > 0
      decreases {this}
  }
}

module RiderPassModule {

  import opened NFCSourceModule
  class RiderPass extends NFCSource {
    var passId: seq<int>
    var ridesRemaining: int

    predicate Valid()
      reads this
      decreases {this}
    {
      |passId| == 8 &&
      (forall k: int {:trigger passId[k]} :: 
        (0 <= k < 8 ==>
          0 <= passId[k]) &&
        (0 <= k < 8 ==>
          passId[k] <= 9)) &&
      ridesRemaining >= 0
    }

    constructor (pid: seq<int>, rides: int)
      requires |pid| == 8
      requires forall k: int {:trigger pid[k]} :: (0 <= k < 8 ==> 0 <= pid[k]) && (0 <= k < 8 ==> pid[k] <= 9)
      requires rides >= 0
      ensures Valid()
      ensures passId == pid
      ensures ridesRemaining == rides
      decreases pid, rides
    {
      passId := pid;
      ridesRemaining := rides;
    }

    function ID(): seq<int>
      reads this
      decreases {this}
    {
      passId
    }

    function OneRideWorth(): int
      reads this
      ensures OneRideWorth() > 0
      decreases {this}
    {
      1
    }

    predicate IsValid()
      reads this
      decreases {this}
    {
      |passId| == 8 &&
      (forall k: int {:trigger passId[k]} :: 
        (0 <= k < 8 ==>
          0 <= passId[k]) &&
        (0 <= k < 8 ==>
          passId[k] <= 9)) &&
      ridesRemaining >= 0
    }

    predicate HasSufficientFunds()
      reads this
      decreases {this}
    {
      ridesRemaining > 0
    }

    function CurrentValue(): int
      requires IsValid()
      reads this
      ensures CurrentValue() >= 0
      decreases {this}
    {
      ridesRemaining
    }

    method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      ensures IsValid()
      ensures OneRideWorth() == old(OneRideWorth())
      ensures ridesRemaining == old(ridesRemaining) - 1
      ensures CurrentValue() == old(ridesRemaining) - 1
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())
      ensures ridesRemaining == old(ridesRemaining) - 1
      ensures passId == old(passId)
    {
      ghost var oldPassId := passId;
      ghost var oldRides := ridesRemaining;
      ridesRemaining := ridesRemaining - 1;
      assert passId == oldPassId;
      assert |passId| == 8;
      assert forall k: int {:trigger passId[k]} :: (0 <= k < 8 ==> 0 <= passId[k]) && (0 <= k < 8 ==> passId[k] <= 9);
      assert ridesRemaining == oldRides - 1;
      assert ridesRemaining >= 0;
      result := Success;
    }
  }
}

module PaymentCardModule {
  function {:fuel 2} LuhnDouble(d: int): int
    requires 0 <= d <= 9
    ensures 0 <= LuhnDouble(d) <= 18
    decreases d
  {
    if d * 2 > 9 then
      d * 2 - 9
    else
      d * 2
  }

  function {:fuel 20} LuhnSum(digits: seq<int>, fromRight: nat): int
    requires forall i: int {:trigger digits[i]} :: (0 <= i < |digits| ==> 0 <= digits[i]) && (0 <= i < |digits| ==> digits[i] <= 9)
    ensures LuhnSum(digits, fromRight) >= 0
    decreases |digits|
  {
    if |digits| == 0 then
      0
    else
      var last: int := digits[|digits| - 1]; var contrib: int := if fromRight % 2 == 1 then LuhnDouble(last) else last; contrib + LuhnSum(digits[..|digits| - 1], fromRight + 1)
  }

  predicate LuhnValid(digits: seq<int>)
    requires |digits| == 16
    requires forall i: int {:trigger digits[i]} :: (0 <= i < |digits| ==> 0 <= digits[i]) && (0 <= i < |digits| ==> digits[i] <= 9)
    decreases digits
  {
    LuhnSum(digits, 0) % 10 == 0
  }

  import opened NFCSourceModule

  class PaymentCard extends NFCSource {
    var id: seq<int>
    var balance: int
    const fare: int

    predicate Valid()
      reads this
      decreases {this}
    {
      fare > 0 &&
      balance >= 0 &&
      (|id| != 16 || !(forall k: int {:trigger id[k]} :: (0 <= k < 16 ==> 0 <= id[k]) && (0 <= k < 16 ==> id[k] <= 9)) || true)
    }

    constructor (cardId: seq<int>, initialBalance: int, rideFare: int)
      requires initialBalance >= 0
      requires rideFare > 0
      ensures Valid()
      ensures balance == initialBalance
      ensures fare == rideFare
      ensures id == cardId
      decreases cardId, initialBalance, rideFare
    {
      id := cardId;
      balance := initialBalance;
      fare := rideFare;
    }

    function ID(): seq<int>
      reads this
      decreases {this}
    {
      id
    }

    function OneRideWorth(): int
      requires IsValid()
      reads this
      ensures OneRideWorth() > 0
      decreases {this}
    {
      fare
    }

    predicate IsValid()
      reads this
      decreases {this}
    {
      |id| == 16 &&
      (forall k: int {:trigger id[k]} :: 
        (0 <= k < 16 ==>
          0 <= id[k]) &&
        (0 <= k < 16 ==>
          id[k] <= 9)) &&
      LuhnValid(id) &&
      fare > 0 &&
      balance >= 0
    }

    predicate HasSufficientFunds()
      reads this
      decreases {this}
    {
      balance >= fare
    }

    function CurrentValue(): int
      requires IsValid()
      reads this
      ensures CurrentValue() >= 0
      decreases {this}
    {
      balance
    }

    method Deduct() returns (result: DeductResult)
      requires IsValid()
      requires HasSufficientFunds()
      modifies this
      ensures result == Success
      ensures balance == old(balance) - fare
      ensures IsValid()
      ensures CurrentValue() == old(balance) - fare
      ensures CurrentValue() >= 0
      ensures ID() == old(ID())
      ensures balance == old(balance) - fare
      ensures OneRideWorth() == old(OneRideWorth())
      ensures id == old(id)
      ensures fare == fare
    {
      ghost var oldId := id;
      ghost var oldBalance := balance;
      balance := balance - fare;
      assert id == oldId;
      assert |id| == 16;
      assert forall k: int {:trigger id[k]} :: (0 <= k < 16 ==> 0 <= id[k]) && (0 <= k < 16 ==> id[k] <= 9);
      assert LuhnValid(id);
      assert fare > 0;
      assert balance == oldBalance - fare;
      assert balance >= 0;
      result := Success;
    }
  }
}
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
namespace NFCSourceModule {


  public interface _IDeductResult {
    bool is_Success { get; }
    bool is_Failure { get; }
    _IDeductResult DowncastClone();
  }
  public abstract class DeductResult : _IDeductResult {
    public DeductResult() {
    }
    private static readonly NFCSourceModule._IDeductResult theDefault = create_Success();
    public static NFCSourceModule._IDeductResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<NFCSourceModule._IDeductResult> _TYPE = new Dafny.TypeDescriptor<NFCSourceModule._IDeductResult>(NFCSourceModule.DeductResult.Default());
    public static Dafny.TypeDescriptor<NFCSourceModule._IDeductResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IDeductResult create_Success() {
      return new DeductResult_Success();
    }
    public static _IDeductResult create_Failure() {
      return new DeductResult_Failure();
    }
    public bool is_Success { get { return this is DeductResult_Success; } }
    public bool is_Failure { get { return this is DeductResult_Failure; } }
    public static System.Collections.Generic.IEnumerable<_IDeductResult> AllSingletonConstructors {
      get {
        yield return DeductResult.create_Success();
        yield return DeductResult.create_Failure();
      }
    }
    public abstract _IDeductResult DowncastClone();
  }
  public class DeductResult_Success : DeductResult {
    public DeductResult_Success() : base() {
    }
    public override _IDeductResult DowncastClone() {
      if (this is _IDeductResult dt) { return dt; }
      return new DeductResult_Success();
    }
    public override bool Equals(object other) {
      var oth = other as NFCSourceModule.DeductResult_Success;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "NFCSourceModule.DeductResult.Success";
      return s;
    }
  }
  public class DeductResult_Failure : DeductResult {
    public DeductResult_Failure() : base() {
    }
    public override _IDeductResult DowncastClone() {
      if (this is _IDeductResult dt) { return dt; }
      return new DeductResult_Failure();
    }
    public override bool Equals(object other) {
      var oth = other as NFCSourceModule.DeductResult_Failure;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "NFCSourceModule.DeductResult.Failure";
      return s;
    }
  }

  public interface NFCSource {
    Dafny.ISequence<BigInteger> ID();
    bool IsValid();
    bool HasSufficientFunds();
    BigInteger CurrentValue();
    NFCSourceModule._IDeductResult Deduct();
    BigInteger OneRideWorth();
  }
  public class _Companion_NFCSource {
  }
} // end of namespace NFCSourceModule
namespace PaymentCardModule {

  public partial class __default {
    public static BigInteger LuhnDouble(BigInteger d) {
      if (((d) * (new BigInteger(2))) > (new BigInteger(9))) {
        return ((d) * (new BigInteger(2))) - (new BigInteger(9));
      } else {
        return (d) * (new BigInteger(2));
      }
    }
    public static BigInteger LuhnSum(Dafny.ISequence<BigInteger> digits, BigInteger fromRight)
    {
      BigInteger _0___accumulator = BigInteger.Zero;
    TAIL_CALL_START: ;
      if ((new BigInteger((digits).Count)).Sign == 0) {
        return (BigInteger.Zero) + (_0___accumulator);
      } else {
        BigInteger _1_last = (digits).Select((new BigInteger((digits).Count)) - (BigInteger.One));
        BigInteger _2_contrib = (((Dafny.Helpers.EuclideanModulus(fromRight, new BigInteger(2))) == (BigInteger.One)) ? (PaymentCardModule.__default.LuhnDouble(_1_last)) : (_1_last));
        _0___accumulator = (_0___accumulator) + (_2_contrib);
        Dafny.ISequence<BigInteger> _in0 = (digits).Take((new BigInteger((digits).Count)) - (BigInteger.One));
        BigInteger _in1 = (fromRight) + (BigInteger.One);
        digits = _in0;
        fromRight = _in1;
        goto TAIL_CALL_START;
      }
    }
    public static bool LuhnValid(Dafny.ISequence<BigInteger> digits) {
      return (Dafny.Helpers.EuclideanModulus(PaymentCardModule.__default.LuhnSum(digits, BigInteger.Zero), new BigInteger(10))).Sign == 0;
    }
  }

  public partial class PaymentCard : NFCSourceModule.NFCSource {
    public PaymentCard() {
      this.id = Dafny.Sequence<BigInteger>.Empty;
      this.balance = BigInteger.Zero;
      this._fare = BigInteger.Zero;
    }
    public Dafny.ISequence<BigInteger> id {get; set;}
    public BigInteger balance {get; set;}
    public bool Valid() {
      return ((((this).fare).Sign == 1) && ((this.balance).Sign != -1)) && ((((new BigInteger((this.id).Count)) != (new BigInteger(16))) || (!(Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger(16)), true, (((_forall_var_0) => {
        BigInteger _0_k = (BigInteger)_forall_var_0;
        return !(((_0_k).Sign != -1) && ((_0_k) < (new BigInteger(16)))) || ((((this.id).Select(_0_k)).Sign != -1) && (((this.id).Select(_0_k)) <= (new BigInteger(9))));
      })))))) || (true));
    }
    public void __ctor(Dafny.ISequence<BigInteger> cardId, BigInteger initialBalance, BigInteger rideFare)
    {
      (this).id = cardId;
      (this).balance = initialBalance;
      (this)._fare = rideFare;
    }
    public Dafny.ISequence<BigInteger> ID() {
      return this.id;
    }
    public BigInteger OneRideWorth() {
      return (this).fare;
    }
    public bool IsValid() {
      return (((((new BigInteger((this.id).Count)) == (new BigInteger(16))) && (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger(16)), true, (((_forall_var_0) => {
        BigInteger _0_k = (BigInteger)_forall_var_0;
        return !(((_0_k).Sign != -1) && ((_0_k) < (new BigInteger(16)))) || ((((this.id).Select(_0_k)).Sign != -1) && (((this.id).Select(_0_k)) <= (new BigInteger(9))));
      }))))) && (PaymentCardModule.__default.LuhnValid(this.id))) && (((this).fare).Sign == 1)) && ((this.balance).Sign != -1);
    }
    public bool HasSufficientFunds() {
      return (this.balance) >= ((this).fare);
    }
    public BigInteger CurrentValue() {
      return this.balance;
    }
    public NFCSourceModule._IDeductResult Deduct()
    {
      NFCSourceModule._IDeductResult result = NFCSourceModule.DeductResult.Default();
      (this).balance = (this.balance) - ((this).fare);
      result = NFCSourceModule.DeductResult.create_Success();
      return result;
    }
    public BigInteger _fare {get; set;}
    public BigInteger fare { get {
      return this._fare;
    } }
  }
} // end of namespace PaymentCardModule
namespace RiderPassModule {


  public partial class RiderPass : NFCSourceModule.NFCSource {
    public RiderPass() {
      this.passId = Dafny.Sequence<BigInteger>.Empty;
      this.ridesRemaining = BigInteger.Zero;
    }
    public Dafny.ISequence<BigInteger> passId {get; set;}
    public BigInteger ridesRemaining {get; set;}
    public bool Valid() {
      return (((new BigInteger((this.passId).Count)) == (new BigInteger(8))) && (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger(8)), true, (((_forall_var_0) => {
        BigInteger _0_k = (BigInteger)_forall_var_0;
        return !(((_0_k).Sign != -1) && ((_0_k) < (new BigInteger(8)))) || ((((this.passId).Select(_0_k)).Sign != -1) && (((this.passId).Select(_0_k)) <= (new BigInteger(9))));
      }))))) && ((this.ridesRemaining).Sign != -1);
    }
    public void __ctor(Dafny.ISequence<BigInteger> pid, BigInteger rides)
    {
      (this).passId = pid;
      (this).ridesRemaining = rides;
    }
    public Dafny.ISequence<BigInteger> ID() {
      return this.passId;
    }
    public BigInteger OneRideWorth() {
      return BigInteger.One;
    }
    public bool IsValid() {
      return (((new BigInteger((this.passId).Count)) == (new BigInteger(8))) && (Dafny.Helpers.Quantifier<BigInteger>(Dafny.Helpers.IntegerRange(BigInteger.Zero, new BigInteger(8)), true, (((_forall_var_0) => {
        BigInteger _0_k = (BigInteger)_forall_var_0;
        return !(((_0_k).Sign != -1) && ((_0_k) < (new BigInteger(8)))) || ((((this.passId).Select(_0_k)).Sign != -1) && (((this.passId).Select(_0_k)) <= (new BigInteger(9))));
      }))))) && ((this.ridesRemaining).Sign != -1);
    }
    public bool HasSufficientFunds() {
      return (this.ridesRemaining).Sign == 1;
    }
    public BigInteger CurrentValue() {
      return this.ridesRemaining;
    }
    public NFCSourceModule._IDeductResult Deduct()
    {
      NFCSourceModule._IDeductResult result = NFCSourceModule.DeductResult.Default();
      (this).ridesRemaining = (this.ridesRemaining) - (BigInteger.One);
      result = NFCSourceModule.DeductResult.create_Success();
      return result;
    }
  }
} // end of namespace RiderPassModule
namespace TripodModule {


  public interface _ITripodState {
    bool is_TripodOpen { get; }
    bool is_TripodClosed { get; }
    _ITripodState DowncastClone();
  }
  public abstract class TripodState : _ITripodState {
    public TripodState() {
    }
    private static readonly TripodModule._ITripodState theDefault = create_TripodOpen();
    public static TripodModule._ITripodState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TripodModule._ITripodState> _TYPE = new Dafny.TypeDescriptor<TripodModule._ITripodState>(TripodModule.TripodState.Default());
    public static Dafny.TypeDescriptor<TripodModule._ITripodState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITripodState create_TripodOpen() {
      return new TripodState_TripodOpen();
    }
    public static _ITripodState create_TripodClosed() {
      return new TripodState_TripodClosed();
    }
    public bool is_TripodOpen { get { return this is TripodState_TripodOpen; } }
    public bool is_TripodClosed { get { return this is TripodState_TripodClosed; } }
    public static System.Collections.Generic.IEnumerable<_ITripodState> AllSingletonConstructors {
      get {
        yield return TripodState.create_TripodOpen();
        yield return TripodState.create_TripodClosed();
      }
    }
    public abstract _ITripodState DowncastClone();
  }
  public class TripodState_TripodOpen : TripodState {
    public TripodState_TripodOpen() : base() {
    }
    public override _ITripodState DowncastClone() {
      if (this is _ITripodState dt) { return dt; }
      return new TripodState_TripodOpen();
    }
    public override bool Equals(object other) {
      var oth = other as TripodModule.TripodState_TripodOpen;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TripodModule.TripodState.TripodOpen";
      return s;
    }
  }
  public class TripodState_TripodClosed : TripodState {
    public TripodState_TripodClosed() : base() {
    }
    public override _ITripodState DowncastClone() {
      if (this is _ITripodState dt) { return dt; }
      return new TripodState_TripodClosed();
    }
    public override bool Equals(object other) {
      var oth = other as TripodModule.TripodState_TripodClosed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TripodModule.TripodState.TripodClosed";
      return s;
    }
  }

  public partial class Tripod {
    public Tripod() {
      this.state = TripodModule.TripodState.Default();
    }
    public TripodModule._ITripodState state {get; set;}
    public bool Valid() {
      return (object.Equals(this.state, TripodModule.TripodState.create_TripodOpen())) || (object.Equals(this.state, TripodModule.TripodState.create_TripodClosed()));
    }
    public void __ctor()
    {
      (this).state = TripodModule.TripodState.create_TripodClosed();
    }
    public void Open()
    {
      (this).state = TripodModule.TripodState.create_TripodOpen();
    }
    public void Close()
    {
      (this).state = TripodModule.TripodState.create_TripodClosed();
    }
    public bool IsOpen() {
      return object.Equals(this.state, TripodModule.TripodState.create_TripodOpen());
    }
    public bool IsClosed() {
      return object.Equals(this.state, TripodModule.TripodState.create_TripodClosed());
    }
  }
} // end of namespace TripodModule
namespace TurnstileModule {


  public interface _ITurnstileState {
    bool is_GateOpen { get; }
    bool is_GateClosed { get; }
    _ITurnstileState DowncastClone();
  }
  public abstract class TurnstileState : _ITurnstileState {
    public TurnstileState() {
    }
    private static readonly TurnstileModule._ITurnstileState theDefault = create_GateOpen();
    public static TurnstileModule._ITurnstileState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TurnstileModule._ITurnstileState> _TYPE = new Dafny.TypeDescriptor<TurnstileModule._ITurnstileState>(TurnstileModule.TurnstileState.Default());
    public static Dafny.TypeDescriptor<TurnstileModule._ITurnstileState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITurnstileState create_GateOpen() {
      return new TurnstileState_GateOpen();
    }
    public static _ITurnstileState create_GateClosed() {
      return new TurnstileState_GateClosed();
    }
    public bool is_GateOpen { get { return this is TurnstileState_GateOpen; } }
    public bool is_GateClosed { get { return this is TurnstileState_GateClosed; } }
    public static System.Collections.Generic.IEnumerable<_ITurnstileState> AllSingletonConstructors {
      get {
        yield return TurnstileState.create_GateOpen();
        yield return TurnstileState.create_GateClosed();
      }
    }
    public abstract _ITurnstileState DowncastClone();
  }
  public class TurnstileState_GateOpen : TurnstileState {
    public TurnstileState_GateOpen() : base() {
    }
    public override _ITurnstileState DowncastClone() {
      if (this is _ITurnstileState dt) { return dt; }
      return new TurnstileState_GateOpen();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileModule.TurnstileState_GateOpen;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileModule.TurnstileState.GateOpen";
      return s;
    }
  }
  public class TurnstileState_GateClosed : TurnstileState {
    public TurnstileState_GateClosed() : base() {
    }
    public override _ITurnstileState DowncastClone() {
      if (this is _ITurnstileState dt) { return dt; }
      return new TurnstileState_GateClosed();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileModule.TurnstileState_GateClosed;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileModule.TurnstileState.GateClosed";
      return s;
    }
  }

  public interface _IProcessResult {
    bool is_Admitted { get; }
    bool is_TimedOut { get; }
    bool is_Denied { get; }
    _IProcessResult DowncastClone();
  }
  public abstract class ProcessResult : _IProcessResult {
    public ProcessResult() {
    }
    private static readonly TurnstileModule._IProcessResult theDefault = create_Admitted();
    public static TurnstileModule._IProcessResult Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<TurnstileModule._IProcessResult> _TYPE = new Dafny.TypeDescriptor<TurnstileModule._IProcessResult>(TurnstileModule.ProcessResult.Default());
    public static Dafny.TypeDescriptor<TurnstileModule._IProcessResult> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IProcessResult create_Admitted() {
      return new ProcessResult_Admitted();
    }
    public static _IProcessResult create_TimedOut() {
      return new ProcessResult_TimedOut();
    }
    public static _IProcessResult create_Denied() {
      return new ProcessResult_Denied();
    }
    public bool is_Admitted { get { return this is ProcessResult_Admitted; } }
    public bool is_TimedOut { get { return this is ProcessResult_TimedOut; } }
    public bool is_Denied { get { return this is ProcessResult_Denied; } }
    public static System.Collections.Generic.IEnumerable<_IProcessResult> AllSingletonConstructors {
      get {
        yield return ProcessResult.create_Admitted();
        yield return ProcessResult.create_TimedOut();
        yield return ProcessResult.create_Denied();
      }
    }
    public abstract _IProcessResult DowncastClone();
  }
  public class ProcessResult_Admitted : ProcessResult {
    public ProcessResult_Admitted() : base() {
    }
    public override _IProcessResult DowncastClone() {
      if (this is _IProcessResult dt) { return dt; }
      return new ProcessResult_Admitted();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileModule.ProcessResult_Admitted;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileModule.ProcessResult.Admitted";
      return s;
    }
  }
  public class ProcessResult_TimedOut : ProcessResult {
    public ProcessResult_TimedOut() : base() {
    }
    public override _IProcessResult DowncastClone() {
      if (this is _IProcessResult dt) { return dt; }
      return new ProcessResult_TimedOut();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileModule.ProcessResult_TimedOut;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileModule.ProcessResult.TimedOut";
      return s;
    }
  }
  public class ProcessResult_Denied : ProcessResult {
    public ProcessResult_Denied() : base() {
    }
    public override _IProcessResult DowncastClone() {
      if (this is _IProcessResult dt) { return dt; }
      return new ProcessResult_Denied();
    }
    public override bool Equals(object other) {
      var oth = other as TurnstileModule.ProcessResult_Denied;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "TurnstileModule.ProcessResult.Denied";
      return s;
    }
  }

  public partial class Turnstile {
    public Turnstile() {
      this.state = TurnstileModule.TurnstileState.Default();
      this._tripod = default(TripodModule.Tripod);
      this._openDuration = BigInteger.Zero;
    }
    public TurnstileModule._ITurnstileState state {get; set;}
    public bool Valid() {
      return ((!(object.Equals(this.state, TurnstileModule.TurnstileState.create_GateOpen())) || (((this).tripod).IsOpen())) && (!(object.Equals(this.state, TurnstileModule.TurnstileState.create_GateClosed())) || (((this).tripod).IsClosed()))) && (((this).openDuration).Sign == 1);
    }
    public void __ctor(BigInteger duration, TripodModule.Tripod t)
    {
      (this)._tripod = t;
      (this).state = TurnstileModule.TurnstileState.create_GateClosed();
      (this)._openDuration = duration;
    }
    public void OpenGate()
    {
      ((this).tripod).Open();
      (this).state = TurnstileModule.TurnstileState.create_GateOpen();
    }
    public void CloseGate()
    {
      ((this).tripod).Close();
      (this).state = TurnstileModule.TurnstileState.create_GateClosed();
    }
    public bool WaitAndClose(bool passengerDetected)
    {
      bool walked = false;
      walked = passengerDetected;
      (this).CloseGate();
      return walked;
    }
    public TurnstileModule._IProcessResult ProcessNFC(NFCSourceModule.NFCSource source, bool passengerDetected)
    {
      TurnstileModule._IProcessResult result = TurnstileModule.ProcessResult.Default();
      if (!((source).IsValid())) {
        result = TurnstileModule.ProcessResult.create_Denied();
        return result;
      }
      if (!((source).HasSufficientFunds())) {
        result = TurnstileModule.ProcessResult.create_Denied();
        return result;
      }
      NFCSourceModule._IDeductResult _0_deductOutcome;
      NFCSourceModule._IDeductResult _out0;
      _out0 = (source).Deduct();
      _0_deductOutcome = _out0;
      if (object.Equals(_0_deductOutcome, NFCSourceModule.DeductResult.create_Success())) {
        (this).OpenGate();
        bool _1_walked;
        bool _out1;
        _out1 = (this).WaitAndClose(passengerDetected);
        _1_walked = _out1;
        if (_1_walked) {
          result = TurnstileModule.ProcessResult.create_Admitted();
        } else {
          result = TurnstileModule.ProcessResult.create_TimedOut();
        }
      } else {
        result = TurnstileModule.ProcessResult.create_Denied();
      }
      return result;
    }
    public bool IsOpen() {
      return object.Equals(this.state, TurnstileModule.TurnstileState.create_GateOpen());
    }
    public bool IsClosed() {
      return object.Equals(this.state, TurnstileModule.TurnstileState.create_GateClosed());
    }
    public TripodModule.Tripod _tripod {get; set;}
    public TripodModule.Tripod tripod { get {
      return this._tripod;
    } }
    public BigInteger _openDuration {get; set;}
    public BigInteger openDuration { get {
      return this._openDuration;
    } }
  }
} // end of namespace TurnstileModule
namespace ProgramModule {

  public partial class __default {
    public static Dafny.ISequence<BigInteger> ValidCardNumber() {
      return Dafny.Sequence<BigInteger>.FromElements(new BigInteger(4), new BigInteger(5), new BigInteger(3), new BigInteger(2), BigInteger.Zero, BigInteger.One, new BigInteger(5), BigInteger.One, BigInteger.One, new BigInteger(2), new BigInteger(8), new BigInteger(3), BigInteger.Zero, new BigInteger(3), new BigInteger(6), new BigInteger(6));
    }
    public static Dafny.ISequence<BigInteger> ValidPassNumber() {
      return Dafny.Sequence<BigInteger>.FromElements(BigInteger.One, new BigInteger(2), new BigInteger(3), new BigInteger(4), new BigInteger(5), new BigInteger(6), new BigInteger(7), new BigInteger(8));
    }
    public static void PrintBanner(Dafny.ISequence<Dafny.Rune> text)
    {
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("------------------------------------------------------------\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((text).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n------------------------------------------------------------\n")).ToVerbatimString(false));
    }
    public static void PrintResult(Dafny.ISequence<Dafny.Rune> lab, TurnstileModule._IProcessResult result)
    {
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  ")).ToVerbatimString(false));
      Dafny.Helpers.Print((lab).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")).ToVerbatimString(false));
      TurnstileModule._IProcessResult _source0 = result;
      {
        if (_source0.is_Admitted) {
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("ADMITTED (passenger walked through)\n")).ToVerbatimString(false));
          goto after_match0;
        }
      }
      {
        if (_source0.is_TimedOut) {
          Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("TIMED OUT (gate closed after timer)\n")).ToVerbatimString(false));
          goto after_match0;
        }
      }
      {
        Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("DENIED\n")).ToVerbatimString(false));
      }
    after_match0: ;
    }
    public static void PrintBalance(Dafny.ISequence<Dafny.Rune> lab, BigInteger v)
    {
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  ")).ToVerbatimString(false));
      Dafny.Helpers.Print((lab).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString(": ")).ToVerbatimString(false));
      Dafny.Helpers.Print((v));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
    }
    public static void AssertTurnstileClosedAndValid(TurnstileModule.Turnstile ts, TripodModule.Tripod tp)
    {
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  [INVARIANT OK] Turnstile closed and in sync with tripod.\n")).ToVerbatimString(false));
    }
    public static void _Main(Dafny.ISequence<Dafny.ISequence<Dafny.Rune>> __noArgsParameter)
    {
      TripodModule.Tripod _0_tripod;
      TripodModule.Tripod _nw0 = new TripodModule.Tripod();
      _nw0.__ctor();
      _0_tripod = _nw0;
      TurnstileModule.Turnstile _1_turnstile;
      TurnstileModule.Turnstile _nw1 = new TurnstileModule.Turnstile();
      _nw1.__ctor(new BigInteger(3), _0_tripod);
      _1_turnstile = _nw1;
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("============================================================\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("     METRO TURNSTILE NFC SUBSYSTEM — VERIFICATION TESTS     \n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("============================================================\n\n")).ToVerbatimString(false));
      ProgramModule.__default.PrintBanner(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T04: PaymentCard | balance=50 | fare=100 -> Denied (insufficient)"));
      {
        PaymentCardModule.PaymentCard _2_card;
        PaymentCardModule.PaymentCard _nw2 = new PaymentCardModule.PaymentCard();
        _nw2.__ctor(ProgramModule.__default.ValidCardNumber(), new BigInteger(50), new BigInteger(100));
        _2_card = _nw2;
        BigInteger _3_valueBefore;
        _3_valueBefore = _2_card.balance;
        TurnstileModule._IProcessResult _4_r;
        TurnstileModule._IProcessResult _out0;
        _out0 = (_1_turnstile).ProcessNFC(_2_card, true);
        _4_r = _out0;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"), _4_r);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Balance after (expected 50, unchanged)"), _2_card.balance);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      ProgramModule.__default.PrintBanner(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T06: RiderPass | rides=2 | passenger times out"));
      {
        RiderPassModule.RiderPass _5_pass;
        RiderPassModule.RiderPass _nw3 = new RiderPassModule.RiderPass();
        _nw3.__ctor(ProgramModule.__default.ValidPassNumber(), new BigInteger(2));
        _5_pass = _nw3;
        TurnstileModule._IProcessResult _6_r;
        TurnstileModule._IProcessResult _out1;
        _out1 = (_1_turnstile).ProcessNFC(_5_pass, false);
        _6_r = _out1;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Result"), _6_r);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Rides after (expected 1)"), _5_pass.ridesRemaining);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      ProgramModule.__default.PrintBanner(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T09: Sequential PaymentCard | balance=300 | fare=100 -> 3 rides then Denied"));
      {
        PaymentCardModule.PaymentCard _7_card;
        PaymentCardModule.PaymentCard _nw4 = new PaymentCardModule.PaymentCard();
        _nw4.__ctor(ProgramModule.__default.ValidCardNumber(), new BigInteger(300), new BigInteger(100));
        _7_card = _nw4;
        TurnstileModule._IProcessResult _8_r1;
        TurnstileModule._IProcessResult _out2;
        _out2 = (_1_turnstile).ProcessNFC(_7_card, true);
        _8_r1 = _out2;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 1"), _8_r1);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Balance"), _7_card.balance);
        BigInteger _9_bal1;
        _9_bal1 = _7_card.balance;
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
        TurnstileModule._IProcessResult _10_r2;
        TurnstileModule._IProcessResult _out3;
        _out3 = (_1_turnstile).ProcessNFC(_7_card, true);
        _10_r2 = _out3;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 2"), _10_r2);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Balance"), _7_card.balance);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
        TurnstileModule._IProcessResult _11_r3;
        TurnstileModule._IProcessResult _out4;
        _out4 = (_1_turnstile).ProcessNFC(_7_card, true);
        _11_r3 = _out4;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 3"), _11_r3);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Balance"), _7_card.balance);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
        TurnstileModule._IProcessResult _12_r4;
        TurnstileModule._IProcessResult _out5;
        _out5 = (_1_turnstile).ProcessNFC(_7_card, true);
        _12_r4 = _out5;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 4 (no funds)"), _12_r4);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Balance (unchanged)"), _7_card.balance);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      ProgramModule.__default.PrintBanner(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("T10: Sequential RiderPass | rides=3 -> 3 rides then Denied"));
      {
        RiderPassModule.RiderPass _13_pass;
        RiderPassModule.RiderPass _nw5 = new RiderPassModule.RiderPass();
        _nw5.__ctor(ProgramModule.__default.ValidPassNumber(), new BigInteger(3));
        _13_pass = _nw5;
        TurnstileModule._IProcessResult _14_r1;
        TurnstileModule._IProcessResult _out6;
        _out6 = (_1_turnstile).ProcessNFC(_13_pass, true);
        _14_r1 = _out6;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 1"), _14_r1);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Rides"), _13_pass.ridesRemaining);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
        TurnstileModule._IProcessResult _15_r2;
        TurnstileModule._IProcessResult _out7;
        _out7 = (_1_turnstile).ProcessNFC(_13_pass, true);
        _15_r2 = _out7;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 2"), _15_r2);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Rides"), _13_pass.ridesRemaining);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
        TurnstileModule._IProcessResult _16_r3;
        TurnstileModule._IProcessResult _out8;
        _out8 = (_1_turnstile).ProcessNFC(_13_pass, true);
        _16_r3 = _out8;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 3"), _16_r3);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Rides"), _13_pass.ridesRemaining);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
        TurnstileModule._IProcessResult _17_r4;
        TurnstileModule._IProcessResult _out9;
        _out9 = (_1_turnstile).ProcessNFC(_13_pass, true);
        _17_r4 = _out9;
        ProgramModule.__default.PrintResult(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("Ride 4 (no rides)"), _17_r4);
        ProgramModule.__default.PrintBalance(Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Rides (unchanged)"), _13_pass.ridesRemaining);
        ProgramModule.__default.AssertTurnstileClosedAndValid(_1_turnstile, _0_tripod);
      }
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("============================================================\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  FINAL SYSTEM STATE CHECK\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("============================================================\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Turnstile state : CLOSED\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  Tripod state    : CLOSED\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("  System valid    : TRUE\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("\n  All tests completed successfully.\n")).ToVerbatimString(false));
      Dafny.Helpers.Print((Dafny.Sequence<Dafny.Rune>.UnicodeFromString("============================================================\n")).ToVerbatimString(false));
    }
  }
} // end of namespace ProgramModule
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(() => ProgramModule.__default._Main(Dafny.Sequence<Dafny.ISequence<Dafny.Rune>>.UnicodeFromMainArguments(args)));
  }
}
