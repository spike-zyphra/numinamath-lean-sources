import Mathlib

theorem algebra_177270 {f : ℝ → ℝ} (hf : ∀ x, f x = x - ⌊x⌋) :
    Function.Periodic f 1 := by
  unfold Function.Periodic
  intro x
  rw [hf, hf]
  simp [Int.floor_add_one]
  <;> ring_nf <;> simp [Int.floor_add_one]
  <;> ring