import Mathlib

open Real

theorem algebra_20783 {x : ℝ} (hx : x = 1 / (sqrt 2 + sqrt 8 + sqrt 32)) :
    IsLeast {n | ∃ A B : ℤ, n = A + B ∧ x = sqrt A / B} 16 := by

  have h1 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    have h2 : (Real.sqrt 8) ^ 2 = 8 := Real.sq_sqrt (show (0 : ℝ) ≤ (8 : ℝ) by norm_num)
    have h3 : (2 * Real.sqrt 2) ^ 2 = 8 := by
      calc
        (2 * Real.sqrt 2) ^ 2 = 4 * (Real.sqrt 2 ^ 2) := by ring
        _ = 4 * (2 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        _ = (8 : ℝ) := by norm_num
    have h4 : Real.sqrt 8 ≥ 0 := by positivity
    have h5 : (2 * Real.sqrt 2) ≥ 0 := by positivity
    have h6 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
      nlinarith [h2, h3]
    exact h6

  have h2 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
    have h3 : (Real.sqrt 32) ^ 2 = 32 := Real.sq_sqrt (show (0 : ℝ) ≤ (32 : ℝ) by norm_num)
    have h4 : (4 * Real.sqrt 2) ^ 2 = 32 := by
      calc
        (4 * Real.sqrt 2) ^ 2 = 16 * (Real.sqrt 2 ^ 2) := by ring
        _ = 16 * (2 : ℝ) := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        _ = (32 : ℝ) := by norm_num
    have h5 : Real.sqrt 32 ≥ 0 := by positivity
    have h6 : (4 * Real.sqrt 2) ≥ 0 := by positivity
    have h7 : Real.sqrt 32 = 4 * Real.sqrt 2 := by
      nlinarith [h3, h4]
    exact h7

  have h3 : Real.sqrt 2 + Real.sqrt 8 + Real.sqrt 32 = 7 * Real.sqrt 2 := by
    rw [h1, h2]
    ring

  have h4 : x = Real.sqrt 2 / 14 := by
    rw [hx]
    have h5 : Real.sqrt 2 + Real.sqrt 8 + Real.sqrt 32 = 7 * Real.sqrt 2 := h3
    rw [h5]
    have h6 : Real.sqrt 2 > 0 := by positivity
    field_simp
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num : (0 : ℝ) ≤ (2 : ℝ)), Real.sqrt_nonneg 2]

  constructor
  · -- Show 16 is in the set
    use 2, 14
    constructor
    · norm_num
    · rw [h4]
      all_goals norm_num

  · -- Show 16 is the minimal
    intro n hn
    rcases hn with ⟨A, B, hn1, h_eq⟩
    by_contra h
    push_neg at h
    have h5 : A + (B : ℤ) < (16 : ℤ) := by linarith

    have h6 : B > 0 := by
      by_contra h7
      push_neg at h7
      have h8 : (B : ℝ) ≤ 0 := by exact_mod_cast show (B : ℝ) ≤ 0 by exact_mod_cast show B ≤ 0 by omega
      have h9 : Real.sqrt (A : ℝ) / (B : ℝ) ≤ 0 := by
        have h10 : Real.sqrt (A : ℝ) ≥ 0 := Real.sqrt_nonneg (A : ℝ)
        have h11 : (B : ℝ) ≤ 0 := h8
        apply div_nonpos_of_nonneg_of_nonpos
        · linarith
        · linarith
      have h10 : Real.sqrt (2 : ℝ) / (14 : ℝ) > 0 := by
        have h11 : Real.sqrt (2 : ℝ) > 0 := by positivity
        have h12 : (14 : ℝ) > 0 := by norm_num
        positivity
      have h11 : Real.sqrt (A : ℝ) / (B : ℝ) > 0 := by
        linarith [h_eq, h10]
      linarith

    have h7 : A ≥ 0 := by
      by_contra h8
      push_neg at h8
      have h12 : Real.sqrt (A : ℝ) = 0 := by
        have h13 : (A : ℝ) < (0 : ℝ) := by exact_mod_cast show (A : ℝ) < (0 : ℝ) by exact_mod_cast show A < (0 : ℤ) by omega
        have h14 : Real.sqrt (A : ℝ) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith
      have h15 : Real.sqrt (2 : ℝ) / (14 : ℝ) > 0 := by
        have h11 : Real.sqrt (2 : ℝ) > 0 := by positivity
        have h12 : (14 : ℝ) > 0 := by norm_num
        positivity
      have h16 : Real.sqrt (A : ℝ) / (B : ℝ) = 0 := by
        rw [h12]
        all_goals norm_num
      have h17 : Real.sqrt (2 : ℝ) / (14 : ℝ) = 0 := by
        linarith [h_eq, h16]
      linarith

    have h9 : Real.sqrt (2 : ℝ) * (B : ℝ) = 14 * Real.sqrt (A : ℝ) := by
      have h10 : Real.sqrt (2 : ℝ) / 14 = Real.sqrt (A : ℝ) / (B : ℝ) := by
        linarith [h4, h_eq]
      have h11 : (B : ℝ) > 0 := by exact_mod_cast show (B : ℝ) > 0 by exact_mod_cast show B > 0 by omega
      have h12 : Real.sqrt (2 : ℝ) * (B : ℝ) = 14 * Real.sqrt (A : ℝ) := by
        field_simp at h10 ⊢
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num : (0 : ℝ) < 2)]
      linarith

    have h14 : (2 : ℝ) * (B : ℝ) ^ 2 = (196 : ℝ) * (A : ℝ) := by
      have h11 : (Real.sqrt (2 : ℝ) * (B : ℝ)) ^ 2 = (14 * Real.sqrt (A : ℝ)) ^ 2 := by
        rw [h9]
      have h12 : (Real.sqrt (2 : ℝ) * (B : ℝ)) ^ 2 = (2 : ℝ) * (B : ℝ) ^ 2 := by
        calc
          (Real.sqrt (2 : ℝ) * (B : ℝ)) ^ 2 = (Real.sqrt (2 : ℝ) ^ 2) * (B : ℝ) ^ 2 := by ring
          _ = (2 : ℝ) * (B : ℝ) ^ 2 := by
            rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h13 : (14 * Real.sqrt (A : ℝ)) ^ 2 = (196 : ℝ) * (A : ℝ) := by
        calc
          (14 * Real.sqrt (A : ℝ)) ^ 2 = 196 * (Real.sqrt (A : ℝ) ^ 2) := by ring
          _ = 196 * (A : ℝ) := by
            rw [Real.sq_sqrt (show (0 : ℝ) ≤ (A : ℝ) by
              have h14 : (A : ℝ) ≥ 0 := by
                have h15 : Real.sqrt (A : ℝ) ≥ 0 := Real.sqrt_nonneg (A : ℝ)
                have h16 : (A : ℝ) ≥ 0 := by
                  by_contra h17
                  push_neg at h17
                  have h18 : Real.sqrt (A : ℝ) = 0 := by
                    rw [Real.sqrt_eq_zero']
                    nlinarith
                  have h19 : Real.sqrt (2 : ℝ) * (B : ℝ) = 0 := by
                    nlinarith [h9, h18]
                  have h20 : Real.sqrt (2 : ℝ) > 0 := by positivity
                  have h21 : (B : ℝ) ≤ 0 := by
                    nlinarith
                  have h22 : (B : ℝ) > 0 := by exact_mod_cast show (B : ℝ) > 0 by exact_mod_cast show B > 0 by omega
                  linarith
                linarith
              linarith
            )]
      nlinarith

    have h15 : 2 * (B : ℤ) ^ 2 = 196 * (A : ℤ) := by
      have h16 : (2 : ℝ) * (B : ℝ) ^ 2 = (196 : ℝ) * (A : ℝ) := h14
      have h17 : (2 : ℤ) * (B : ℤ) ^ 2 = (196 : ℤ) * (A : ℤ) := by
        exact_mod_cast h14
      omega

    have h20 : A + B < 16 := by omega
    have h22 : B ≤ 15 := by omega
    interval_cases B <;> try { 
      omega
    } <;> try { 
      have : A ≤ 15 := by omega
      interval_cases A <;> omega
    }