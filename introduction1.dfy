method Abs(x: int) returns (y: int)
    //postcondition
    ensures y >= 0 && (x >= 0 ==> y == x) && (x < 0 ==> y == -x)
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
    }
}

method TestingAbs()
{
    var v := Abs(3);
    assert v >= 0; 
    assert v == 3;  //fixed functionality (works)
}

method MultipleReturns(x: int, y: int) returns (more: int, less:int)
    //precondition
    requires y > 0
    ensures less < x 
    ensures more > x
{
    more := x + y;
    less := x - y;
}

method Max(a: int, b:int) returns (c: int)
    requires a != b
    ensures (c > a || c > b) && (c == a || c == b)
{
    if a > b {
        c := a;
    } else {
        c := b;
    }
}

method TestingMax()
{
    var v := Max(-1, 1);
    assert v == 1; 

    var x := Max(-2,-1);
    assert x == -1;

    var z := Max(0, 1);
    assert z == 1;

    var a := Max(-1, 0);
    assert a == 0;

    var b:= Max(1,3);
    assert b == 3;
}



