trait Card
{
    ghost predicate Valid()
        reads this

    function Value() : int
        reads this
        requires Valid()
        ensures 1 <= Value() <= 14
}

class NumberCard extends Card
{
    const rank : int

    ghost predicate Valid()
        reads this
    {
        2 <= rank <= 10 ||
        rank == 14
    }

    constructor(num : int)
        requires 2 <= num <= 10 || num == 14
        ensures rank == num
        ensures Valid()
    {
        rank := num;
    }

    function Value() : int
        reads this
        requires Valid()
        ensures rank == Value()
        ensures 2 <= Value() <= 10 || Value() == 14
    {
        rank
    }
}

class FaceCard extends Card
{
    const rank : int
    const face : FaceRank

    ghost predicate Valid()
        reads this
    {
        11 <= rank <= 13
    }

    constructor(num : int)
        requires 11 <= num <= 13 
        ensures rank == num
        ensures face == RankToFace(num)
        ensures Valid()
    {
        rank := num;
        face := RankToFace(num);
    }

    function Value() : int
        reads this
        requires Valid()
        ensures rank == Value()
        ensures 11 <= Value() <= 14
    {
        rank
    }
}

datatype FaceRank = Jack | Queen | King

function FaceRankToInt(f: FaceRank): int
  ensures 11 <= FaceRankToInt(f) <= 13
{
  match f
  case Jack  => 11
  case Queen => 12
  case King  => 13
}

function RankToFace(rank: int): FaceRank
  requires 11 <= rank <= 13
  ensures match rank
    case 11 => RankToFace(rank) == Jack
    case 12 => RankToFace(rank) == Queen
    case 13 => RankToFace(rank) == King
{
  match rank
  case 11 => Jack
  case 12 => Queen 
  case 13 => King
}

/*class Joker extends Card
{
    const rank : int

    ghost predicate Valid()
        reads this
    {
        rank == 15
    }

    constructor(num : int)
        requires num == 15
        ensures rank == num
        ensures Valid()
    {
        rank := num;
    }

    function Value() : int   // <- Function should provide equal or stronger postcondition than a trait
        reads this
        requires Valid()
        ensures rank == Value()
        ensures Value() == 15
    {
        rank
    }
}*/

method SumOfHand(cards : seq<Card>) returns (sum : int)
    requires 0 < |cards|
    requires forall k : int :: 0 <= k < |cards| ==> cards[k].Valid() == true
    ensures |cards| <= sum 
{
    sum := 0;
    var i := 0;
    while i < |cards|
        invariant 0 <= i <= |cards|
        invariant i <= sum
    {
        var v := cards[i].Value();
        sum := sum + v;
        i := i + 1;
    }
}

method Main()
{
    var hand : seq<Card> := [];
    var card1 := new NumberCard(2);
    var card2 := new NumberCard(8);
    var card3 := new FaceCard(12);
    var card4 := new NumberCard(5);
    var card5 := new NumberCard(14);
    hand := hand + [card1];
    hand := hand + [card2];
    hand := hand + [card3];
    hand := hand + [card4];
    hand := hand + [card5];

    // sum = 41
    var result := SumOfHand(hand);
    print "Sum of hand result: ", result, "\n";
}

