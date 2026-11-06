import Mathlib

theorem algebra_162327 {a b : ℝ} (h : ∀ x : ℝ, |x^2 + a * x + b| ≤ |2 * x^2 + 4 * x - 30|) :
    a = 2 ∧ b = -15 := by 
  have h1 := h 3
  have h2 := h (-5 : ℝ)
  norm_num [abs_le] at h1 h2
  have h3 : (9 + 3 * a + b) ≤ (0 : ℝ) := by
    linarith [h1]
  have h4 : (9 + 3 * a + b) ≥ (0 : ℝ) := by
    linarith [h1]
  have h5 : (25 - 5 * a + b) ≤ (0 : ℝ) := by
    linarith [h2]
  have h6 : (25 - 5 * a + b) ≥ (0 : ℝ) := by
    linarith [h2]
  have eq1 : 9 + 3 * a + b = 0 := by
    linarith
  -- From eq1 : $9 + 3a + b = 0$
  have eq2 : 25 - 5 * a + b = 0 := by
    linarith
  -- From eq2 : $25 - 5a + b = 0$
  have ha : a = 2 := by
    linarith [eq1, eq2]
  have hb : b = -15 := by
    linarith [eq1, ha]
  exact ⟨ha, hb⟩