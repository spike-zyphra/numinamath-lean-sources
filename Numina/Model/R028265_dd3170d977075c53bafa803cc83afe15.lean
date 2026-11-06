import Mathlib

theorem algebra_10849 (a : ℕ → ℝ) (ha : ∀ n, ∑ i in Finset.range n, a i = n ^ 2 + 3 * n + 4) :
    ∑ i in (Finset.Icc 1 21).filter Odd, a i = 268 := by 
  have h1 := ha 0
  simp at h1
  all_goals
    linarith