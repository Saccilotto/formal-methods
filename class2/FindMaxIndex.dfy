// Encontrar o índíce do index elemento do array
method FindMaxIndex(a : array<int>) returns (i : int)
    requires a.Length > 0 
    ensures i >= 0 && i < a.Length  //indice válido
    ensures forall j :: 0 <= j < a.Length ==> a[i] >= a[j]   // é o maio elemento
{
    var index := 0;
    i := 0;
    while index < a.Length 
        invariant i >= 0 && i < a.Length
        invariant index >= 0 && index <= a.Length   // loop + 1(quando sai do loop)
        invariant forall j :: j >= 0  && j < index ==> a[i] >= a[j] 
    {
        if a[index] > a[i]
        {
            i := index;
        }
        index := index + 1;
    }
}

