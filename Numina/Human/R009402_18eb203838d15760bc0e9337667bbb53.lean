import Mathlib

/-How many positive four-digit integers are divisible by $8$?-/
theorem number_theory_17075 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ 8 ∣ n} = 1125 := by
  -- An integer is divisible by $8$ if and only if the number formed from its last three digits is divisible by $8$.
  -- Thus, the number of possibilities for the last three digits is equal to the number of three-digit multiples of $8$.  Since $1000 = 8\cdot 125$, we find that there are $125$ such multiples.  Since the thousands digit of our four-digit integer must be nonzero, there are $9$ possibilities for the thousands digit.  Altogether, $9 \cdot 125 = \boxed{1125}$ four-digit integers are divisible by $8$.
  apply Set.ncard_eq_of_bijective
  case f => exact fun x h => x * 8 + 1000
  simp
  intro a ha₁ ha₂ ha₃
  use (a - 1000) / 8
  omega
  simp
  omega
  simp
