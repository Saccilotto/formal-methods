ghost function Pot(a:nat, b:nat):nat
{
    if b == 0
    then 1
    else a * Pot(a, b-1)
}

method PotenciaRapida(a:nat, b:nat) returns (r:nat)
    ensures r == Pot(a, b)
{
    var c := a;
    var i := b;
    r := 1;
    while i > 0
    {
        if i % 2 != 0
        {
            r := r * c;
            i := i - 1;
        }
        c := c * c;
        i := i/2;
    }
}

method PotenciaLenta(a:nat, b:nat) returns (r:nat)
    ensures r == Pot(a, b)
{
    if b == 0 
    {
        return 1;
    }
    var potant := PotenciaLenta(a, b-1);
    return a * potant;
}

