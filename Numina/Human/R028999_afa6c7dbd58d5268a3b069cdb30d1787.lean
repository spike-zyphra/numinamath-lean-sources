import Mathlib

/-If positive real numbers a,b satisfy a^b=b^a, and a<1, prove that a= b. Analysis Directly proving a= b by constant identity transformation is quite difficult and not easy to start. Instead, consider weakening the proposition, first proving a weaker conclusion a≥b,then proving a≤b,thus deducing a=b -/
theorem algebra_161331 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ b = b ^ a) (h1 : a < 1) : a ≥ b ∧ b ≥ a := by

  -- prove step by step--
  have h2 : b < 1 := by
    by_contra h2
    push_neg at h2
    have h3 : a < 1 := by linarith
    have h4 : Real.log a < 0 := by
      have h5 : Real.log a < Real.log 1 := Real.log_lt_log (by linarith) (by linarith)
      have h6 : Real.log 1 = 0 := Real.log_one
      linarith
    have h5 : Real.log b ≥ 0 := by
      have h6 : 1 ≤ b := by linarith
      have h7 : Real.log b ≥ Real.log 1 := Real.log_le_log (by linarith) (by linarith)
      have h8 : Real.log 1 = 0 := Real.log_one
      linarith
    have h6 : a ^ b = b ^ a := h
    -- use log to simplify --
    have h7 : b * Real.log a = a * Real.log b := by
      have h8 : a > 0 := by linarith
      have h9 : b > 0 := by linarith
      have h10 : a ^ b > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      have h11 : b ^ a > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      have h12 : Real.log (a ^ b) = Real.log (b ^ a) := by
        rw [h]
      have h13 : Real.log (a ^ b) = b * Real.log a := by
        rw [Real.log_rpow]
        all_goals linarith
      have h14 : Real.log (b ^ a) = a * Real.log b := by
        rw [Real.log_rpow]
        all_goals linarith
      linarith
    nlinarith [mul_self_nonneg (Real.log a), mul_self_nonneg (Real.log b), h7]
  constructor
  · -- Proof that $a \geq b$ --
    by_contra h2
    push_neg at h2
    have h3 : Real.log a < Real.log b := by
      have h4 : a < b := by linarith
      have h5 : a > 0 := by linarith
      have h6 : b > 0 := by linarith
      exact Real.log_lt_log (by linarith) (by linarith)
    have h4 : Real.log b < 0 := by
      have h5 : b < 1 := by linarith [h2]
      have h6 : Real.log b < Real.log 1 := Real.log_lt_log (by linarith) (by linarith)
      have h7 : Real.log 1 = 0 := Real.log_one
      linarith
    have h5 : b * Real.log a = a * Real.log b := by -- use log to simplify --
      have h6 : a > 0 := by linarith
      have h7 : b > 0 := by linarith
      have h8 : a ^ b > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      have h9 : b ^ a > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      have h10 : Real.log (a ^ b) = Real.log (b ^ a) := by
        rw [h]
      have h11 : Real.log (a ^ b) = b * Real.log a := by
        rw [Real.log_rpow]
        all_goals linarith
      have h12 : Real.log (b ^ a) = a * Real.log b := by
        rw [Real.log_rpow]
        all_goals linarith
      linarith
    have h6 : a > 0 := by linarith
    have h7 : b > 0 := by linarith
    nlinarith [h3, h4, h5, h6, h7]
  · -- Proof that $b \geq a$, by symmetry, it's similar to above--
    by_contra h2
    push_neg at h2
    have h3 : Real.log b < Real.log a := by
      have h4 : b < a := by linarith
      have h5 : b > 0 := by linarith
      have h6 : a > 0 := by linarith
      exact Real.log_lt_log (by linarith) (by linarith)
    have h4 : Real.log a < 0 := by
      have h5 : a < 1 := by linarith [h1]
      have h6 : Real.log a < Real.log 1 := Real.log_lt_log (by linarith) (by linarith)
      have h7 : Real.log 1 = 0 := Real.log_one
      linarith
    have h5 : b * Real.log a = a * Real.log b := by
      have h6 : a > 0 := by linarith
      have h7 : b > 0 := by linarith
      have h8 : a ^ b > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      have h9 : b ^ a > 0 := by
        apply Real.rpow_pos_of_pos
        linarith
      have h10 : Real.log (a ^ b) = Real.log (b ^ a) := by
        rw [h]
      have h11 : Real.log (a ^ b) = b * Real.log a := by
        rw [Real.log_rpow]
        all_goals linarith
      have h12 : Real.log (b ^ a) = a * Real.log b := by
        rw [Real.log_rpow]
        all_goals linarith
      linarith
    have h6 : Real.log b < 0 := by
      have h7 : b < 1 := by nlinarith [h2]
      have h8 : Real.log b < Real.log 1 := Real.log_lt_log (by linarith) (by linarith)
      have h9 : Real.log 1 = 0 := Real.log_one
      linarith
    have h7 : b > 0 := by linarith
    have h8 : a > 0 := by linarith
    nlinarith [h3, h4, h5, h6, h7, h8]