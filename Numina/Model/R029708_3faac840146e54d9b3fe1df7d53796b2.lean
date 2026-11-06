import Mathlib

theorem algebra_253445 (x : ℝ) : (2^(3*x) : ℝ) - 8/(2^(3*x)) - 6*(2^x - 1/(2^(x-1))) = 1 ↔ x = 1 := by
  constructor
  · -- Assume the equation holds, prove x = 1
    intro h
    have eq1 : (2 : ℝ) ^ (3 * x) = ((2 : ℝ) ^ x) ^ 3 := by
      calc
        (2 : ℝ) ^ (3 * x) = (2 : ℝ) ^ (x * (3 : ℝ)) := by ring_nf
        _ = ((2 : ℝ) ^ x) ^ 3 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul]
          ring_nf
          all_goals linarith
    have eq2 : (1 / (2 : ℝ) ^ (x - 1 : ℝ) ) = (2 / (2 : ℝ) ^ x) := by
      have eq3 : (2 : ℝ) ^ (x - 1 : ℝ) = (2 ^ x / (2 : ℝ)) := by
        rw [show x - 1 = x - (1 : ℝ) by ring_nf]
        rw [Real.rpow_sub]
        norm_num
        all_goals linarith
      rw [eq3]
      field_simp [(show (2 : ℝ) ^ x ≠ 0 by
        positivity)]
    rw [eq1, eq2] at h
    have h3 : ((2 : ℝ) ^ x) ^ 3 - 8 / ((2 : ℝ) ^ x) ^ 3 - 6 * ((2 : ℝ) ^ x - (2 / ((2 : ℝ) ^ x))) - (1 : ℝ) = 0 := by linarith
    have eq3 : ((2 : ℝ) ^ x) > 0 := by positivity
    have h4 : ((2 : ℝ) ^ x) ^ 6 - 6 * ((2 : ℝ) ^ x) ^ 4 + 12 * ((2 : ℝ) ^ x) ^ 2 - ((2 : ℝ) ^ x) ^ 3 - 8 = 0 := by
      have h5 : ((2 : ℝ) ^ x) ^ 3 - 8 / ((2 : ℝ) ^ x) ^ 3 - 6 * ((2 : ℝ) ^ x - (2 / ((2 : ℝ) ^ x))) - (1 : ℝ) = 0 := h3
      have h6 : ((2 : ℝ) ^ x) ≠ 0 := by positivity
      field_simp at h5 ⊢
      nlinarith [sq_nonneg ((2 : ℝ) ^ x), sq_nonneg (((2 : ℝ) ^ x) ^ 2 - 2)]
    have eq5 : (((2 : ℝ) ^ x) ^ 2 - 2 ) ^ 3 = ((2 : ℝ) ^ x) ^ 3 := by
      nlinarith [h4]
    have eq5' : (((2 : ℝ) ^ x) ^ 2 - 2 ) ^ 3 - ((2 : ℝ) ^ x) ^ 3 = 0 := by
      linarith [eq5]
    have h7 : (((2 : ℝ) ^ x) ^ 2 - 2 - (2 : ℝ) ^ x) * ( (((2 : ℝ) ^x ) ^ 2 - 2 ) ^ 2 + ( (2 : ℝ) ^x ) * ( ((2 : ℝ) ^x ) ^ 2 - 2 ) + ( (2 : ℝ)^x ) ^ 2 ) = 0 := by
      ring_nf at eq5' ⊢
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- First factor is zero.
      have eq6 : ((2 : ℝ) ^ x) ^ 2 - ((2 : ℝ) ^ x) - 2 = 0 := by
        linarith
      have eq7 : ((2 : ℝ) ^ x) = (2 : ℝ) := by
        nlinarith [sq_nonneg ((2 : ℝ) ^ x - (2 : ℝ)), sq_nonneg ((2 : ℝ) ^ x + (1 : ℝ)), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) x]
      have h9 : x = 1 := by
        apply_fun (Real.logb (2 : ℝ)) at eq7
        simp at eq7 ⊢
        linarith
      exact h9
    · -- Second factor is zero.
      have h9 : (((2 : ℝ) ^x ) ^ 2 - 2 ) ^ 2 + ( (2 : ℝ) ^x ) * ( ((2 : ℝ) ^x ) ^ 2 - 2 ) + ( (2 : ℝ)^x ) ^ 2 = 0 := by
        linarith
      have h10 : (((2 : ℝ) ^x ) ^ 2 - 2 ) ^ 2 = 0 := by
        nlinarith [sq_nonneg (((2 : ℝ) ^x ) ^ 2 - 2), sq_nonneg ((2 : ℝ) ^x), sq_nonneg (( (2 : ℝ)^x ) ^ 2 - 2 + (2 : ℝ) ^x), sq_nonneg (( (2 : ℝ)^x ) ^ 2 + (2 : ℝ) ^x), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) x]
      have h11 : ((2 : ℝ) ^x ) ^ 2 - 2 = 0 := by
        nlinarith
      have eq7 : ((2 : ℝ) ^ x) = (2 : ℝ) := by
        nlinarith [sq_nonneg ((2 : ℝ) ^x - (2 : ℝ)), Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) x, h11]
      have h9 : x = 1 := by
        apply_fun (Real.logb (2 : ℝ)) at eq7
        simp at eq7 ⊢
        linarith
      exact h9
  · -- Backward implication
    intro h
    rw [h]
    norm_num