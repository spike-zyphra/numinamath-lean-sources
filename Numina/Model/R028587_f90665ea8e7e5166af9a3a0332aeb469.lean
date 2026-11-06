import Mathlib

open Real Set
open scoped Real

theorem calculus_14886 {n : ℕ} (hn : n ∈ Finset.range 10) (z : ℂ) (hz : z = (tan (π/5) + I)/(tan (π/5) - I)) (hzroot : z ^ 10 = 1 ∧ ∀ j < 10, z ^ j ≠ 1):
    n = 3 := by
  have h2 := hzroot.right 0 (by linarith)
  simp [hz, pow_zero] at h2
  all_goals tauto