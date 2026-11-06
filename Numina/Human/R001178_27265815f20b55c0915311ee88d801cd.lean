import Mathlib

/-Let $\boxed{N}$ mean the number of whole number divisors of $N$. For example, $\boxed{3}=2$, because $3$ has two divisors, $1$ and $3.$ Find the value of \[\boxed{\boxed{11}\times\boxed{20}}\]-/
theorem algebra_20887 : ( (11:Nat).divisors.card) * ( (20:Nat).divisors.card) = 12 := by
  --展开divisors和card的定义，直到可以直接构建等式相等
  have left : (11:Nat).divisors.card = 2 := by
    simp[Nat.divisors,Finset.Ico,LocallyFiniteOrder.finsetIco]
    simp[Finset.filter,List.length]
  have right : (20:Nat).divisors.card = 6 := by
    simp[Nat.divisors,Finset.Ico,LocallyFiniteOrder.finsetIco]
    simp[Finset.filter,List.length]
  rw[left,right]
