import Mathlib

open Real

lemma lemma_1 {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (h : 2 * a ^ 2 = c ^ 2) :
    1 / a + 1 / a + 1 / c ≥ (2 + 3 * √2) / (a + a + c) := by
  have h1 : c = Real.sqrt 2 * a := by
    have h2 : c ^ 2 = 2 * a ^ 2 := by linarith
    have h3 : c = Real.sqrt (2 * a^2) := by
      rw [← h2]
      field_simp [hc]
    have h4 : Real.sqrt (2 * a ^ 2) = Real.sqrt 2 * a := by
      have h5 : 0 ≤ a := by linarith
      have h6 : Real.sqrt (2 * a ^ 2) = Real.sqrt 2 * Real.sqrt (a ^ 2) := by
        rw [Real.sqrt_mul (by nlinarith)]
      have h7 : Real.sqrt (a ^ 2) = a := by
        rw [Real.sqrt_sq (by linarith)]
      rw [h6, h7]
    rw [h4] at h3
    linarith
  have hx : 1 / a + 1 / a + 1 / c - (2 + 3 * Real.sqrt 2) / (a + a + c) ≥ 0 := by
    have hx2 : 1 / a + 1 / a + 1 / c - (2 + 3 * Real.sqrt 2) / (a + a + c) =
          (2 * a^2 + 3 * a * c + 2 * c^2 - 3 * Real.sqrt 2 * a * c) / (a * c * (a + a + c)) := by
      field_simp
      <;> nlinarith
    rw [hx2]
    have hy : 2 * a^2 + 3 * a * c + 2 * c^2 - 3 * Real.sqrt 2 * a * c ≥ 0 := by
      have h5 : c = Real.sqrt 2 * a := h1
      rw [h5]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ 2)]
    apply div_nonneg
    linarith
    positivity
  linarith


theorem inequalities_601265 (a b c : ℝ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a ≤ b) (h₄ : b < c) (h₅ : a^2 + b^2 = c^2) :
    1 / a + 1 / b + 1 / c ≥ (2 + 3 * √2) / (a + b + c) := by
  have h6 : a + b > c := by 
      nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₁, sq_pos_of_pos h₂, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  have h8 : a > 0 := h₀
  have h9 : b > 0 := h₁
  have h10 : c > 0 := h₂
  have h11 : 0 < a + b + c := by positivity
  have h11' : 1 / a + 1 / b + 1 / c - (2 + 3 * √2) / (a + b + c) ≥ 0 := by
    have h100 : 0 < a * b * c := by positivity
    have hx1 : 1 / a + 1 / b + 1 / c - (2 + 3 * √2) / (a + b + c) =
        ( (a + b + c) * (b * c + a * c + a * b) - (2 + 3 * √2) * (a * b * c) ) / ( (a * b * c) * (a + b + c) ) := by
      field_simp
      <;> ring
    rw [hx1]
    have hx2 : (a + b + c) * (b * c + a * c + a * b) - (2 + 3 * √2) * (a * b * c) ≥ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1), sq_nonneg (c - a * Real.sqrt 2), sq_nonneg (c - b * Real.sqrt 2), sq_nonneg (a + b - c), sq_nonneg (a - b), 
            sq_nonneg (a * c - b * c), sq_nonneg (a * c - a * c), sq_nonneg (a -  b),
            mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂, Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
            sq_nonneg (a * Real.sqrt 2 - b * Real.sqrt 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
          ]
    apply div_nonneg
    linarith
    positivity
  linarith