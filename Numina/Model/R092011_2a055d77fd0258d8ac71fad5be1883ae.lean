import Mathlib

theorem algebra_151863 (ω : ℂ) (hω : ω^2007 = 1) (hω' : ∀ k < 2007, ω^k ≠ 1) :
    (2^2007 - 1) * ∑ j ∈ Finset.range 2000, 1 / (2 - ω^(j + 1)) = 2005 * 2^2006 + 1 := by
  have h1 := hω' 0 (by norm_num)
  simp at h1
  all_goals contradiction