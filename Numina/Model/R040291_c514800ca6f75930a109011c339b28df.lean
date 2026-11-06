import Mathlib

open Real

theorem algebra_279025 {f : ℝ → ℝ} (hf : ∀ x, f x = x - ⌊x⌋) :
    ∀ x, f (x + 1) = f x := by
  intro x
  rw [hf, hf]
  simp [Int.floor_add_one]
  <;> ring_nf
  <;> norm_num