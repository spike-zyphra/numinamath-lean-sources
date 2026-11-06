import Mathlib

theorem algebra_98682 {a b : ℝ} {c : ℝ} (h₀ : a ≠ b) (h₁ : c > 0)
    (h₂ : a ^ 4 - 2019 * a = c) (h₃ : b ^ 4 - 2019 * b = c) :
    -Real.sqrt c < a * b ∧ a * b < 0 := by
  have h_mul : (b - a) * ((a + b) * (a ^ 2 + b ^ 2) - 2019) = 0 := by
    ring_nf
    <;> nlinarith [h₂, h₃]
  have hb : b - a ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h_eq : (a + b) * (a ^ 2 + b ^ 2) - 2019 = 0 := by
    apply congrArg (fun x => x / (b - a)) at h_mul
    field_simp [show b - a ≠ 0 by exact hb] at h_mul
    <;> nlinarith
  have h_eq2 : (a + b) * (a ^ 2 + b ^ 2) = 2019 := by linarith
  have h4 : a * b < 0 := by
    nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
      intro h
      apply h₀
      nlinarith), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2 - 2 * (a * b)), sq_nonneg (a + b), sq_nonneg (a - b), h_eq2]
  have h5 : -Real.sqrt c < a * b := by
    have h6 : (a * b) ^ 2 < c := by
      nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
        intro h
        apply h₀
        nlinarith), sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2 - 2 * (a * b)), sq_nonneg (a + b), sq_nonneg (a - b), h_eq2, h₂, h₃, Real.sqrt_nonneg c, Real.sq_sqrt (show 0 ≤ (c : ℝ) by linarith)]
    have h7 : Real.sqrt c > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h8 : Real.sqrt c ^ 2 = c := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [h6, h7, h8, Real.sqrt_nonneg c]
  constructor
  · linarith [h5, show Real.sqrt c > 0 by apply Real.sqrt_pos.mpr; linarith]
  · linarith [h4]