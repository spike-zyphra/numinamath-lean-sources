import Mathlib


theorem algebra_21184 {a b : ℕ}
    (h : √(√56 * √126) = a * √b) (hb : Squarefree b) : a + b = 23 := by


  have h1 : Real.sqrt (Real.sqrt 56 * Real.sqrt 126) = Real.sqrt (Real.sqrt (56 * 126 : ℝ)) := by
    have h2 : Real.sqrt 56 * Real.sqrt 126 = Real.sqrt (56 * 126 : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h2]

  have h2 : Real.sqrt (Real.sqrt (56 * 126 : ℝ)) = Real.sqrt (84 : ℝ) := by
    have h3 : Real.sqrt (56 * 126 : ℝ) = (84 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3]

  have h3 : Real.sqrt (84 : ℝ) = (2 : ℝ) * Real.sqrt (21 : ℝ) := by
    have h4 : Real.sqrt (84 : ℝ) = Real.sqrt (4 * 21 : ℝ) := by norm_num
    rw [h4]
    have h5 : Real.sqrt (4 * 21 : ℝ) = Real.sqrt (4 : ℝ) * Real.sqrt (21 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num)]
    rw [h5]
    have h6 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h6]

  rw [h1, h2, h3] at h

  have h4 : (a : ℝ) * Real.sqrt (b : ℝ) = (2 : ℝ) * Real.sqrt (21 : ℝ) := by
    linarith

  have h5 : (a * Real.sqrt (b : ℝ)) ^ 2 = ((2 : ℝ) * Real.sqrt (21 : ℝ)) ^ 2 := by
    rw [h4]

  have h6 : (a * Real.sqrt (b : ℝ)) ^ 2 = (a : ℝ) ^ 2 * (b : ℝ) := by
    calc
      (a * Real.sqrt (b : ℝ)) ^ 2 = (a : ℝ) ^ 2 * (Real.sqrt (b : ℝ) ^ 2) := by ring
      _ = (a : ℝ) ^ 2 * (b : ℝ) := by
        rw [Real.sq_sqrt]
        have hb2 : (b : ℝ) ≥ 0 := by exact_mod_cast show (0 : ℕ) ≤ b by omega
        nlinarith

  have h7 : ((2 : ℝ) * Real.sqrt (21 : ℝ)) ^ 2 = (84 : ℝ) := by
    calc
      ((2 : ℝ) * Real.sqrt (21 : ℝ)) ^ 2 = (4 : ℝ) * (Real.sqrt (21 : ℝ) ^ 2) := by ring
      _ = (4 : ℝ) * (21 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      _ = (84 : ℝ) := by norm_num

  rw [h6, h7] at h5

  have h8 : (a : ℝ) ^ 2 * (b : ℝ) = (84 : ℝ) := by
    linarith

  have h10 : a ^ 2 * b = 84 := by
    have h9 : (a ^ 2 * b : ℝ) = (84 : ℝ) := by
      have h10 : (a : ℝ) ^ 2 * (b : ℝ) = (a ^ 2 * b : ℝ) := by
        simp [mul_pow]
      rw [h10] at h8
      linarith
    exact_mod_cast h9

  have h11 : a ≤ 9 := by
    by_contra h12
    push_neg at h12
    have h13 : a > 9 := by linarith
    have h14 : a ^ 2 > 81 := by
      have h15 : a > 9 := h13
      have h16 : a ≥ 10 := by omega
      have h17 : a ^ 2 ≥ 100 := by
        have h18 : a ≥ 10 := h16
        have h19 : a ^ 2 ≥ 10 ^ 2 := by
          apply Nat.pow_le_pow_of_le_left h18 2
        norm_num at h19 ⊢
        linarith
      nlinarith
    have h18 : a ^ 2 * b > 84 := by
      have hb2 : b ≥ 1 := by
        by_contra h18
        push_neg at h18
        have : b < 1 := by linarith
        have : b = 0 := by omega
        rw [this] at h10
        nlinarith
      have h17 : a ^ 2 > 84 := by
        nlinarith
      nlinarith
    nlinarith

  interval_cases a <;> try { 
    omega
  } <;> try { 
    have h13 : b ≤ 84 := by
      nlinarith
    interval_cases b <;> norm_num at h10 hb ⊢ 
    <;> tauto
  }