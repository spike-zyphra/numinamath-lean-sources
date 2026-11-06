import Mathlib

theorem algebra_220937 {a b : ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : (a + 3 * b).1 * (7 * a - 5 * b).1 + (a + 3 * b).2 * (7 * a - 5 * b).2 = 0)
    (h2 : (a - 4 * b).1 * (7 * a - 2 * b).1 + (a - 4 * b).2 * (7 * a - 2 * b).2 = 0) :
    Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2))) = Real.pi / 3 := by
  have eq1 : 7 * (a.1 ^ 2 + a.2 ^ 2) + 16 * (a.1 * b.1 + a.2 * b.2) - 15 * (b.1 ^ 2 + b.2 ^ 2) = 0 := by 
    simp [mul_add, add_mul] at h1 
    nlinarith 
  have eq2 : 7 * (a.1 ^ 2 + a.2 ^ 2) - 30 * (a.1 * b.1 + a.2 * b.2) + 8 * (b.1 ^ 2 + b.2 ^ 2) = 0 := by 
    simp [mul_add, add_mul] at h2 
    nlinarith
  have eq3 : 2 * (a.1 * b.1 + a.2 * b.2) = b.1 ^ 2 + b.2 ^ 2 := by
    nlinarith [eq1, eq2]
  have eq4 : a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by 
    nlinarith [eq1, eq2]
  have eq5 : (a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2) = (2 * (a.1 * b.1 + a.2 * b.2)) ^ 2 := by
    have h7 : a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := eq4
    have h8 : b.1 ^ 2 + b.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by
      nlinarith [eq3]
    calc
      (a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2) = (2 * (a.1 * b.1 + a.2 * b.2)) * (2 * (a.1 * b.1 + a.2 * b.2)) := by 
        rw [h7, h8]
      _ = (2 * (a.1 * b.1 + a.2 * b.2)) ^ 2 := by 
        ring
  have eq6 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = 2 * (a.1 * b.1 + a.2 * b.2) := by
    calc 
      Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2)
          = Real.sqrt ((a.1 ^ 2 + a.2 ^ 2) * (b.1 ^ 2 + b.2 ^ 2)) := by
            rw [← Real.sqrt_mul (by positivity)]
          _ = Real.sqrt ((2 * (a.1 * b.1 + a.2 * b.2)) ^ 2) := by
            rw [eq5]
          _ = (2 * (a.1 * b.1 + a.2 * b.2)) := by
            rw [Real.sqrt_sq]
            all_goals nlinarith [show a.1 * b.1 + a.2 * b.2 ≥ 0 by nlinarith]
          _ = 2 * (a.1 * b.1 + a.2 * b.2) := by ring
  have h3 : a.1 * b.1 + a.2 * b.2 > 0 := by 
    by_contra h
    push_neg at h 
    have h7 : a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := eq4
    have h8 : b.1 ^ 2 + b.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by 
      nlinarith [eq3]
    have h9 : a.1 ^ 2 + a.2 ^ 2 = 0 := by 
      nlinarith [h, sq_nonneg (a.1), sq_nonneg (a.2), sq_nonneg (b.1), sq_nonneg (b.2)]
    have h_eq1 : a.1 = 0 := by 
      nlinarith [sq_nonneg (a.1), sq_nonneg (a.2), h9]
    have h_eq2 : a.2 = 0 := by 
      nlinarith [sq_nonneg (a.1), sq_nonneg (a.2), h9]
    have h0 : a = (0, 0) := by 
      simp [Prod.ext_iff, h_eq1, h_eq2]
    have hne : a = (0) := h0
    contradiction
  have eq7 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) = 1 / 2 := by
    rw [eq6]
    field_simp [h3]
    <;> nlinarith 
  rw [eq7]
  have h5 : Real.arccos (1 / 2) = Real.pi / 3 := by
    have h6 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [← h6]
    apply Real.arccos_cos
    all_goals linarith [Real.pi_pos]
  exact h5