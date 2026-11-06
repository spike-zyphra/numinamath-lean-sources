import Mathlib

theorem algebra_94889 {f : ℝ → ℝ} (hf : ∀ x, f x = (x + 1) / (x - 1)) :
    ∀ x, x ^ 2 ≠ 1 → f (-x) = 1 / f x := by
  intro x h
  have h1 : f (-x) = ((-x) + 1) / ((-x) - 1) := by
    rw [hf]
  have h2 : f x = (x + 1) / (x - 1) := by
    rw [hf]
  rw [h1, h2]
  have h3 : x - 1 ≠ 0 := by
    intro h4
    have : x ^ 2 = 1 := by
      have h1 : x = 1 := by linarith
      rw [h1]
      norm_num
    contradiction
  have h4 : x + 1 ≠ 0 := by
    intro h5
    have : x ^ 2 = 1 := by
      have h1 : x = -1 := by linarith
      rw [h1]
      norm_num
    contradiction
  have h5 : (-x) - 1 ≠ 0 := by
    intro h6
    have : x = -1 := by linarith
    have h6 : x ^ 2 = 1 := by
      rw [this]
      norm_num
    contradiction
  field_simp [(show (-x) - 1 ≠ 0 by assumption), h4, h3]
  <;> ring_nf <;> field_simp [(show (-x) - 1 ≠ 0 by assumption), h4, h3]
  <;> nlinarith