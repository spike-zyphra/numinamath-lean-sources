import Mathlib

theorem algebra_30716 {b c : ℤ} (f : ℝ → ℝ) (hf : ∀ n : ℤ, f n ≥ 0)
    (h : ∀ x : ℝ, f x = x ^ 2 + 2 * b * x + c) :
    ∀ x : ℚ, f x ≥ 0 := by
  have h1 : (c : ℝ) ≥ (b : ℝ) ^ 2 := by
    have h2 := hf (-b)
    simp [h] at h2
    nlinarith
  intro x
  have h4 : f (x) = (x : ℝ) ^ 2 + 2 * (b : ℝ) * (x : ℝ) + (c : ℝ) := by
    specialize h (x)
    simpa using h
  rw [h4]
  have h5 : (c : ℝ) ≥ (b : ℝ) ^ 2 := h1
  have hfx : (x : ℝ) ^ 2 + 2 * (b : ℝ) * (x : ℝ) + (c : ℝ) ≥ 0 := by
    have h6 : (c : ℝ) ≥ (b : ℝ) ^ 2 := h1
    have h7 : (x : ℝ) ^ 2 + 2 * (b : ℝ) * (x : ℝ) + (c : ℝ) = 
      (x + (b : ℝ)) ^ 2 + (c - (b : ℝ) ^ 2 : ℝ) := by 
      ring
    rw [h7]
    have h8 : (x + (b : ℝ)) ^ 2 ≥ 0 := by 
      apply sq_nonneg
    have h9 : (c - (b : ℝ) ^ 2 : ℝ) ≥ 0 := by 
      linarith
    linarith
  exact_mod_cast hfx