import Mathlib

open Real

theorem inequalities_320650 (a b c : ℝ) (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 < a) (h2 : a ≤ b) (h3 : b ≤ c) :
    logb a b + logb b c + logb c a ≤ logb b a + logb c b + logb a c := by

  have h4 : a > 1 := h1
  have h5 : b ≥ a := h2
  have h6 : c ≥ b := h3
  have h7 : a > 0 := ha.1
  have h8 : b > 0 := hb
  have h9 : c > 0 := hc

  have h10 : logb a b = log b / log a := by field_simp [logb]
  have h11 : logb b c = log c / log b := by field_simp [logb]
  have h12 : logb c a = log a / log c := by field_simp [logb]
  have h13 : logb b a = log a / log b := by field_simp [logb]
  have h14 : logb c b = log b / log c := by field_simp [logb]
  have h15 : logb a c = log c / log a := by field_simp [logb]

  rw [h10, h11, h12, h13, h14, h15]

  have h16 : log a > 0 := by
    apply log_pos
    linarith
  have h19 : 1 < b := by
    nlinarith
  have h17 : log b > 0 := by
    apply log_pos
    linarith
  have h19 : 1 < c := by
    nlinarith
  have h20 : log c > 0 := by
    apply log_pos
    linarith

  have h37 : log b / log a + log c / log b + log a / log c ≤ log a / log b + log b / log c + log c / log a := by
    have h21 : log b ≥ log a := by
      apply Real.log_le_log
      all_goals linarith
    have h22 : log c ≥ log b := by
      apply Real.log_le_log
      all_goals linarith

    have h24 : log b / log a + log c / log b + log a / log c - (log a / log b + log b / log c + log c / log a) ≤ 0 := by
      have h25 : log a > 0 := h16
      have h26 : log b > 0 := h17
      have h27 : log c > 0 := h20
      have h28 : log b ≥ log a := h21
      have h29 : log c ≥ log b := h22

      have h30 : log b / log a + log c / log b + log a / log c - (log a / log b + log b / log c + log c / log a) ≤ 0 := by
        have h31 : log b / log a + log c / log b + log a / log c - (log a / log b + log b / log c + log c / log a) =
            (log b * log b * log c + log c * log c * log a + log a * log a * log b - (log a * log a * log c + log b * log b * log a + log c * log c * log b)) / (log a * log b * log c) := by
          field_simp
          ring
        rw [h31]

        apply div_nonpos_of_nonpos_of_nonneg
        · -- Prove numerator is ≤ 0
          nlinarith [sq_nonneg (log a - log b), sq_nonneg (log a - log c), sq_nonneg (log b - log c), 
            mul_pos h16 h17, mul_pos h16 h20, mul_pos h17 h20, 
            mul_nonneg (show 0 ≤ log a by linarith) (show 0 ≤ log b - log a by linarith), 
            mul_nonneg (show 0 ≤ log b by linarith) (show 0 ≤ log c - log b by linarith)]
        · -- Prove denominator is ≥ 0
          positivity
      linarith
    linarith
  linarith [h37]