import Mathlib

open Real

theorem calculus_246563 (n : ℕ) (hn : n > 0) :
    (sqrt (n + 1) - sqrt n) < 4 / (n ^ ((1 : ℝ) / 3)) := by
  have h1 : (n : ℝ) > 0 := by exact_mod_cast hn
  have h2 : sqrt (n + 1) - sqrt n = 1 / (sqrt (n + 1) + sqrt n) := by
    have h3 : sqrt (n + 1) ^ 2 = (n + 1 : ℝ) := Real.sq_sqrt (by linarith)
    have h4 : sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
    have h5 : sqrt (n + 1) + sqrt n > 0 := by
      have h6 : sqrt (n + 1) > 0 := by
        apply Real.sqrt_pos.2
        linarith
      have h7 : sqrt n > 0 := by
        apply Real.sqrt_pos.2
        linarith
      linarith
    field_simp [show sqrt (n + 1) + sqrt n ≠ 0 by linarith]
    <;> nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg (n : ℝ), h3, h4]
  rw [h2]
  have h3 : (n : ℝ) ^ ((1 : ℝ) / 3) > 0 := by positivity
  have h4 : sqrt (n + 1 : ℝ) + sqrt (n : ℝ) > 0 := by
    have h5 : sqrt (n + 1 : ℝ) > 0 := by apply Real.sqrt_pos.2; linarith
    have h6 : sqrt (n : ℝ) > 0 := by apply Real.sqrt_pos.2; linarith
    linarith [h5, h6]
  have h5 : (n : ℝ) ^ ((1 : ℝ) / 3) < 4 * (sqrt (n : ℝ)) := by
    have h6 : ( (n : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      norm_num
      all_goals linarith
    have h7 : (4 * Real.sqrt (n : ℝ)) ^ 3 = 64 * ( (n : ℝ) ^ (3 / 2 : ℝ) ) := by
      calc
        (4 * Real.sqrt (n : ℝ)) ^ 3 = 64 * (Real.sqrt (n : ℝ) ) ^ 3 := by ring
        _ = 64 * ( (Real.sqrt (n : ℝ)) ^ 2 ) * Real.sqrt (n : ℝ) := by ring
        _ = 64 * (n : ℝ) * Real.sqrt (n : ℝ) := by
          rw [Real.sq_sqrt (by linarith)]
        _ = 64 * ( (n : ℝ) ^ (3 / 2 : ℝ) ) := by
          have h8 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
            have h9 : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
              rw [Real.sqrt_eq_rpow]
            have h10 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
              rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by ring]
              rw [Real.rpow_add]
              ring_nf
              all_goals linarith
            rw [h9] at *
            rw [h10]
            <;> simp
          rw [h8]
          <;> ring
    have h8 : ( (n : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 < (4 * Real.sqrt (n : ℝ)) ^ 3 := by
      have h9 : ( (n : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 = (n : ℝ) := h6
      have h10 : (4 * Real.sqrt (n : ℝ)) ^ 3 = 64 * ( (n : ℝ) ^ (3 / 2 : ℝ) ) := h7
      rw [h9, h10]
      have h11 : (n : ℝ) ^ (3 / 2 : ℝ) > (n : ℝ) / 64 := by
        have h13 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
          have h9 : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
          have h10 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
            rw [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by ring]
            rw [Real.rpow_add]
            ring_nf
            all_goals linarith
          rw [h9] at *
          rw [h10]
          <;> simp
        rw [h13]
        have h14 : Real.sqrt (n : ℝ) > 1 / 64 := by
          have h10 : (n : ℝ) ≥ 1 := by exact_mod_cast (show n ≥ 1 by omega)
          nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith), Real.sqrt_le_sqrt (show (0 : ℝ) ≤ (n : ℝ) by linarith)]
        nlinarith [Real.sqrt_nonneg (n : ℝ)]
      nlinarith [show (n : ℝ) > 0 by exact_mod_cast hn]
    have h9 : (n : ℝ) ^ ((1 : ℝ) / 3) < 4 * Real.sqrt (n : ℝ) := by
      have h10 : ( (n : ℝ) ^ ((1 : ℝ) / 3) ) ^ 3 < (4 * Real.sqrt (n : ℝ)) ^ 3 := h8
      nlinarith [sq_nonneg ( (n : ℝ) ^ ((1 : ℝ) / 3) - 4 * Real.sqrt (n : ℝ) ), Real.sqrt_nonneg (n : ℝ), sq_nonneg ( (n : ℝ) ^ ((1 : ℝ) / 3) ), sq_nonneg (4 * Real.sqrt (n : ℝ) ) ]
    linarith
  have h7 : (n : ℝ) ^ ((1 : ℝ) / 3) < 4 * (sqrt (n + 1) + sqrt (n)) := by
    have h8 : sqrt (n + 1) > sqrt (n : ℝ) := by
      apply Real.sqrt_lt_sqrt
      all_goals linarith
    linarith [h5, h8]
  have h9 : (sqrt (n + 1 : ℝ) + sqrt (n : ℝ)) > 0 := h4
  have h10 : (n : ℝ) ^ ((1 : ℝ) / 3) > 0 := h3
  apply (div_lt_div_iff (by positivity) (by positivity)).mpr
  nlinarith [h7]