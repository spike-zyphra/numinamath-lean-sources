import Mathlib

theorem algebra_153791 {a : ℕ → ℤ} (ha1 : a 1 = 4) (han : ∀ n, a (n + 1) = ∑ i in Finset.range n, a i + 2 * (n + 1) + 1) :
    a 2005 = 11 * 2 ^ 2003 - 2 := by 
  have h1 := han 0
  simp [Finset.sum_range] at h1 
  all_goals
    omega