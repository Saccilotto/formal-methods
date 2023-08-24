method Mult(m:nat, n:nat) returns (a:nat) 
    ensures a == m*n
{
    a := 0;
    var x:nat := m; 
    var y:nat := n;
    while x > 0
        invariant m * n == x * y + a 
    {
        a := a + y;
        x := x - 1;
    }
    
}



