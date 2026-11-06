import Mathlib

theorem algebra_11930 {a b : ℝ} (h₀ : a - b = 2) (h₁ : (1 + b)^2 / (1 + a) + (1 - a)^2 / (1 - b) = 4) :
    a^5 - b^5 = 82 := by
  have h2 : a = b + 2 := by linarith
  have eq1 : 1 + a = b + 3 := by 
    rw [h2]
    linarith
  have eq2 : 1 - a = - (b + 1) := by 
    rw [h2]
    linarith
  have h3 : (b + 3 : ℝ) ≠ 0 := by
    by_contra h
    have hb : b = -3 := by linarith
    have ha : a = -1 := by 
      linarith [h2, hb]
    rw [ha, hb] at h₁
    norm_num [ha, hb] at h₁
  have h4 : (1 - b : ℝ) ≠ 0 := by
    by_contra h
    have hb : b = 1 := by linarith 
    have ha : a = 3 := by 
      linarith [h2, hb]
    rw [ha, hb] at h₁
    norm_num [ha, hb] at h₁
  have eq5 : (1 + b)^2 * (1 - b) + (b + 1)^2 * (b + 3) = 4 * (b + 3) * (1 - b) := by
    have h₁₁ : (1 + b)^2 / (1 + a) + (1 - a)^2 / (1 - b) = 4 := h₁
    rw [show 1 + a = b + 3 by linarith [eq1]] at h₁₁
    have eq6 : (1 - a)^2 = (b + 1)^2 := by
      rw [eq2]
      ring
    rw [eq6] at h₁₁
    have h₇ : b + 3 ≠ 0 := h3
    have h₈ : (1 - b) ≠ 0 := h4
    field_simp [(show b + 3 ≠ 0 by assumption), 
        (show (1 - b : ℝ) ≠ 0 by assumption) 
          ] at h₁₁ ⊢ 
    <;> nlinarith 
  have eq6 : b^2 + 2 * b - 1 = 0 := by
    nlinarith [eq5]
  have eqb2 : b^2 = 1 - 2 * b := by linarith [eq6]
  have eqb3 : b^3 = 5 * b - 2 := by
    calc
      b^3 = b * b^2 := by ring
      _ = b * (1 - 2 * b) := by rw [eqb2]
      _ = b - 2 * b^2 := by ring
      _ = b - 2 * (1 - 2 * b) := by rw [eqb2]
      _ = 5 * b - 2 := by nlinarith
  have eqb4 : b^4 = 5 - 12 * b := by
    calc
      b^4 = b * b^3 := by ring
      _ = b * (5 * b - 2) := by rw [eqb3]
      _ = 5 * b^2 - 2 * b := by ring
      _ = 5 * (1 - 2 * b) - 2 * b := by rw [eqb2]
      _ = 5 - 12 * b := by nlinarith
  have eqb5 : b^5 = 29 * b - 12 := by
    calc 
      b^5 = b * b^4 := by ring 
      _ = b * (5 - 12 * b) := by rw [eqb4]
      _ = 5 * b - 12 * b^2 := by ring
      _ = 5 * b - 12 * (1 - 2 * b) := by rw [eqb2]
      _ = 29 * b - 12 := by nlinarith
  have eqa5 : a^5 = 29 * b + 70 := by
    have ha : a = b + 2 := h2
    rw [ha]
    nlinarith [eqb2, eqb3, eqb4]
  have eq7 : a^5 - b^5 =82 := by
    nlinarith [eqa5, eqb5]
  linarith [eq7]