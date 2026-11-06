import Mathlib

/-Find the sum of the primes between 100 and 200, inclusive, that are 1 or 2 more than a perfect square.-/
theorem algebra_19997:
    (∑ p in (Finset.Icc 100 200).filter (fun n => n.Prime ∧ (let x:ℕ :=Nat.sqrt (n-1);x*x=(n-1)∨ let  x:ℕ :=Nat.sqrt (n-2);x*x=(n-2)) ), p )= 298 := by
    -- 先判断一个数是否是质数，然后再判断它的前一个数或前两个数是否是完全平方数
    -- 利用函数的定义展开证明
      norm_num[Finset.sum,Multiset.sum,Finset.Icc,Multiset.filter,LocallyFiniteOrder.finsetIcc,List.filter]
      