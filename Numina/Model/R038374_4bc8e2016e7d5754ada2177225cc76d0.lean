import Mathlib

theorem algebra_219512 {a b : ℝ × ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : (a.1 - 2 * b.1, a.2 - 2 * b.2) * a = 0) (h2 : (b.1 - 2 * a.1, b.2 - 2 * a.2) * b = 0) :
    Real.pi / 3 = Real.arccos ((a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2))) := by

  have eq1 : a.1 ^ 2 + a.2 ^ 2 - 2 * (a.1 * b.1 + a.2 * b.2) = 0 := by
    simp [Prod.ext_iff, mul_add, mul_sub, sub_mul] at h1 ⊢
    linarith
  have eq2 : b.1 ^ 2 + b.2 ^ 2 - 2 * (a.1 * b.1 + a.2 * b.2) = 0 := by
    simp [Prod.ext_iff, mul_add, mul_sub, sub_mul] at h2 ⊢
    linarith
  have h3 : a.1 ^ 2 + a.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by linarith
  have h4 : b.1 ^ 2 + b.2 ^ 2 = 2 * (a.1 * b.1 + a.2 * b.2) := by linarith
  have h5 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = Real.sqrt (b.1 ^ 2 + b.2 ^ 2) := by
    have h7 : a.1 ^ 2 + a.2 ^ 2 = b.1 ^ 2 + b.2 ^ 2 := by
      nlinarith [h3, h4]
    rw [h7]

  have h10 : (a.1 * b.1 + a.2 * b.2) = (a.1 ^ 2 + a.2 ^ 2) / 2 := by
    nlinarith [h3]

  have ha1_pos : a.1 ^ 2 + a.2 ^ 2 > 0 := by
    by_contra h
    push_neg at h
    have h_z : a.1 = 0 ∧ a.2 = 0 := by
      have ha1_zero : a.1 = 0 := by
        nlinarith [sq_nonneg (a.1), sq_nonneg (a.2)]
      have ha2_zero : a.2 = 0 := by
        nlinarith [sq_nonneg (a.1), sq_nonneg (a.2)]
      exact ⟨ha1_zero, ha2_zero⟩
    have h_zero : a = (0, 0) := by
      simp [ Prod.ext_iff, h_z.1, h_z.2]
    contradiction

  have hb1_pos : b.1 ^ 2 + b.2 ^ 2 > 0 := by
    by_contra h
    push_neg at h
    have h_z : b.1 = 0 ∧ b.2 = 0 := by
      have hb1_zero : b.1 = 0 := by
        nlinarith [sq_nonneg (b.1), sq_nonneg (b.2)]
      have hb2_zero : b.2 = 0 := by
        nlinarith [sq_nonneg (b.1), sq_nonneg (b.2)]
      exact ⟨hb1_zero, hb2_zero⟩
    have h_zero : b = (0, 0) := by
      simp [ Prod.ext_iff, h_z.1, h_z.2]
    contradiction

  have h11 : (a.1 * b.1 + a.2 * b.2) / (Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2)) = 1 / 2 := by

    have h6 : Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = (a.1 ^ 2 + a.2 ^ 2) := by
      have h61 : Real.sqrt (b.1 ^ 2 + b.2 ^ 2) = Real.sqrt (a.1 ^ 2 + a.2 ^ 2) := by
        have h7 : b.1 ^ 2 + b.2 ^ 2 = a.1 ^ 2 + a.2 ^ 2 := by
          nlinarith [h3, h4]
        rw [h7]
      rw [h61]
      have h9 : (Real.sqrt (a.1 ^ 2 + a.2 ^ 2)) ^ 2 = a.1 ^ 2 + a.2 ^ 2 := Real.sq_sqrt (by positivity)
      calc
        Real.sqrt (a.1 ^ 2 + a.2 ^ 2) * Real.sqrt (a.1 ^ 2 + a.2 ^ 2) = (Real.sqrt (a.1 ^ 2 + a.2 ^ 2)) ^ 2 := by ring
        _ = a.1 ^ 2 + a.2 ^ 2 := by rw [h9]

    rw [h6]
    rw [h10]

    have ha1_pos' : a.1 ^ 2 + a.2 ^ 2 ≠ 0 := by linarith
    have : ( (a.1 ^ 2 + a.2 ^ 2) / 2 ) / (a.1 ^ 2 + a.2 ^ 2) = 1 / 2 := by
      field_simp [ha1_pos']
      all_goals nlinarith

    linarith

  rw [h11]
  have h : Real.arccos (1 / 2) = Real.pi / 3 := by
    have h1 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    rw [← h1]
    apply Real.arccos_cos
    all_goals linarith [Real.pi_pos]

  linarith [h, Real.pi_pos]