import Mathlib

theorem algebra_13254 (A : ℕ → ℤ) (hA1 : A 1 = 1) (hA2 : A 2 = 5)
    (hA : ∀ n, A (n + 2) = A (n + 1) + 2 * A n) :
    ∑ i in Finset.Icc 1 20, A i = 2097150 := by 
  norm_num [Finset.sum_Icc_succ_top, hA1, hA2, hA]
  <;> try { all_goals omega }