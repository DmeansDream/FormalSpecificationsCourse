predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

function DigitValue(c: char): nat
{
  if IsDigit(c) then (c as int - '0' as int) as nat else 0
}

predicate DigitsOnly(s: string)
  decreases |s|
{
  |s| == 0 || (IsDigit(s[0]) && DigitsOnly(s[1..]))
}

function LuhnDouble(d: nat): nat
{
  if d * 2 > 9 then d * 2 - 9 else d * 2
}

function LuhnSumFromLeft(s: string, idx: nat): nat
  requires DigitsOnly(s)
  requires idx <= |s|
  decreases |s| - idx
{
  if idx == |s| then
    0
  else
    var d := DigitValue(s[idx]);
    var distanceFromRight := |s| - idx;
    (if distanceFromRight % 2 == 0 then LuhnDouble(d) else d) + LuhnSumFromLeft(s, idx + 1)
}

predicate IsValidPaymentNumber(s: string)
{
  |s| == 16 && DigitsOnly(s) && LuhnSumFromLeft(s, 0) % 10 == 0
}

predicate IsValidPassId(s: string)
{
  |s| == 8 && DigitsOnly(s)
}