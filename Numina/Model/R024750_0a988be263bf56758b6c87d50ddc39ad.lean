import Mathlib

theorem algebra_608149 (ω : ℂ) (hω : ω ^ 2007 = 1) (hω1 : ∀ k < 2007, ω ^ k ≠ 1) :
    (2 ^ 2007 - 1) * ∑ j ∈ Finset.range 2006, 1 / (2 - ω ^ (j + 1)) = 2005 * 2 ^ 2006 + 1 := by
  have h1 := hω1 0 (by linarith)
  simp at h1
  all_goals
    norm_num at h1 ⊢