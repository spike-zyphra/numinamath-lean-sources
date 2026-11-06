import Mathlib

theorem algebra_121238 {a : ℝ} (f : ℝ → ℝ) (hf : f = fun x => 1 / 2 * Real.sin (2 * x) + a * Real.cos (2 * x))
    (h : ∀ x, f (Real.pi / 12 + x) = f (Real.pi / 12 - x)) :
    a = Real.sqrt 3 / 2 := by
  have h1 := h (Real.pi / 12)
  have h2 : f (Real.pi / 12 + Real.pi / 12) = f (Real.pi / 12 - Real.pi / 12) := h1
  rw [hf] at h2
  simp at h2
  have eq1 : (1 / 2 * Real.sin (2 * (Real.pi / 12 + Real.pi / 12)) + a * Real.cos (2 * (Real.pi / 12 + Real.pi / 12))) =
          (1 / 2 * Real.sin (2 * (Real.pi / 12 - Real.pi / 12)) + a * Real.cos (2 * (Real.pi / 12 - Real.pi / 12))) := by
    simpa using h2
  have eq2 : 2 * (Real.pi / 12 + Real.pi / 12) = Real.pi / 3 := by
    ring_nf
  have eq3 : 2 * (Real.pi / 12 - Real.pi / 12) = (0 : ℝ) := by
    ring_nf
  rw [eq2, eq3] at eq1
  have h3 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h5 : Real.sin (0 : ℝ) = 0 := by simp
  have h6 : Real.cos (0 : ℝ) = 1 := by simp
  simp [h3, h4, h5, h6] at eq1
  linarith