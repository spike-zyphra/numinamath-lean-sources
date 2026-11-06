import Mathlib

theorem algebra_21816 {k : ℝ} (f : ℝ → ℝ) (hf : f = fun x => k * x ^ 4 + 9 * x ^ 3 + k * x ^ 2 + 32 * x - 11)
    (h : f (-5) = 4) : k = 2 := by
  rw [hf] at h
  simp at h
  linarith