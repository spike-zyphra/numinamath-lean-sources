import Mathlib

/- Let $a_n = 4n^3 + 6n^2 + 4n + 1.$  Find
\[a_8 + a_9 + a_{10} + \dots + a_{23}.\] -/
theorem algebra_20825 (a : ℕ → ℕ) (ha : a = λ n => 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1) : 
    ∑ i ∈ Finset.Icc 8 23, a i = 327680 := by 
  simp [ha]
  rfl