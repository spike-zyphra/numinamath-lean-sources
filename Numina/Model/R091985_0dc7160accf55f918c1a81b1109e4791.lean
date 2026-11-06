import Mathlib

theorem algebra_136604 {f : ℝ → ℝ} (h : ∀ x, 3 * f x + f (-x) = 4 * Real.sin x * Real.cos x) :
    f = fun x => Real.sin (2 * x) := by
  funext x
  have eq1 := h x
  have eq2 := h (-x)
  simp [show Real.sin (-x) = -Real.sin x by rw [Real.sin_neg], show Real.cos (-x) = Real.cos x by rw [Real.cos_neg] ] at eq2
  have eq3 : f (-x) = 4 * Real.sin x * Real.cos x - 3 * f x := by linarith
  rw [eq3] at eq2
  have eq4 : 8 * f x = 16 * Real.sin x * Real.cos x := by
    linarith
  have hx : f x = 2 * Real.sin x * Real.cos x := by
    linarith
  rw [hx]
  simp [Real.sin_two_mul]
  all_goals linarith