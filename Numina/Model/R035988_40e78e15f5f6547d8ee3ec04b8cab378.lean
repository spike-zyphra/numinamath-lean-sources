import Mathlib

open Real

theorem inequalities_188968 (a b c : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    logb (a + b) (c^2) + logb (b + c) (a^2) + logb (c + a) (b^2) ≥ 3 := by

  have h1 : a + b ≥ 4 := by nlinarith
  have h2 : b + c ≥ 4 := by nlinarith
  have h3 : c + a ≥ 4 := by nlinarith

  have h31 : logb (a + b) (c ^ 2) = 2 * log c / log (a + b) := by
    have h41 : logb (a + b) (c ^ 2) = log (c ^ 2) / log (a + b) := by
      field_simp [logb]
    have h42 : log (c ^ 2) = 2 * log c := by
      simp [log_pow]
    rw [h41, h42]

  have h32 : logb (b + c) (a ^ 2) = 2 * log a / log (b + c) := by
    have h41 : logb (b + c) (a ^ 2) = log (a ^ 2) / log (b + c) := by
      field_simp [logb]
    have h42 : log (a ^ 2) = 2 * log a := by
      simp [log_pow]
    rw [h41, h42]

  have h33 : logb (c + a) (b ^ 2) = 2 * log b / log (c + a) := by
    have h41 : logb (c + a) (b ^ 2) = log (b ^ 2) / log (c + a) := by
      field_simp [logb]
    have h42 : log (b ^ 2) = 2 * log b := by
      simp [log_pow]
    rw [h41, h42]

  have h41 : log (a + b) ≤ log a + log b := by
    have h411 : a + b ≤ a * b := by
      nlinarith [mul_self_nonneg (a - 2), mul_self_nonneg (b - 2), sq_nonneg (a - b), sq_nonneg (a - 2), sq_nonneg (b - 2)]
    have h412 : log (a + b) ≤ log (a * b) := by
      apply Real.log_le_log
      all_goals nlinarith
    have h413 : log (a * b) = log a + log b := by
      rw [log_mul (by linarith) (by linarith)]
    linarith [h412, h413]

  have h42 : log (b + c) ≤ log b + log c := by
    have h421 : b + c ≤ b * c := by
      nlinarith [mul_self_nonneg (b - 2), mul_self_nonneg (c - 2), sq_nonneg (b - c), sq_nonneg (b - 2), sq_nonneg (c - 2)]
    have h422 : log (b + c) ≤ log (b * c) := by
      apply Real.log_le_log
      all_goals nlinarith
    have h423 : log (b * c) = log b + log c := by
      rw [log_mul (by linarith) (by linarith)]
    linarith [h422, h423]

  have h43 : log (c + a) ≤ log c + log a := by
    have h431 : c + a ≤ c * a := by
      nlinarith [mul_self_nonneg (c - 2), mul_self_nonneg (a - 2), sq_nonneg (c - a), sq_nonneg (c - 2), sq_nonneg (a - 2)]
    have h432 : log (c + a) ≤ log (c * a) := by
      apply Real.log_le_log
      all_goals nlinarith
    have h433 : log (c * a) = log c + log a := by
      rw [log_mul (by linarith) (by linarith)]
    linarith [h432, h433]

  have h51 : log a ≥ log 2 := by
    apply Real.log_le_log
    all_goals linarith
  have h52 : log b ≥ log 2 := by
    apply Real.log_le_log
    all_goals linarith
  have h53 : log c ≥ log 2 := by
    apply Real.log_le_log
    all_goals linarith

  have h61 : log 2 > 0 := by
    apply Real.log_pos
    all_goals linarith

  have h71 : log a > 0 := by
    have h711 : log a ≥ log 2 := h51
    have h712 : log 2 > 0 := h61
    linarith
  have h72 : log b > 0 := by
    have h721 : log b ≥ log 2 := h52
    have h722 : log 2 > 0 := h61
    linarith
  have h73 : log c > 0 := by
    have h731 : log c ≥ log 2 := h53
    have h732 : log 2 > 0 := h61
    linarith

  have h101 : 2 * log c / log (a + b) ≥ 2 * log c / (log a + log b) := by
    have h121 : log (a + b) > 0 := by
      have h122 : a + b > 1 := by
        nlinarith
      have h123 : log (a + b) > 0 := by
        apply Real.log_pos
        all_goals linarith
      linarith
    have h124 : log a + log b > 0 := by
      linarith [h71, h72]
    have h125 : log (a + b) ≤ log a + log b := h41
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h73]

  have h102 : 2 * log a / log (b + c) ≥ 2 * log a / (log b + log c) := by
    have h121 : log (b + c) > 0 := by
      have h122 : b + c > 1 := by
        nlinarith
      have h123 : log (b + c) > 0 := by
        apply Real.log_pos
        all_goals linarith
      linarith
    have h124 : log b + log c > 0 := by
      linarith [h72, h73]
    have h125 : log (b + c) ≤ log b + log c := h42
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h71]

  have h103 : 2 * log b / log (c + a) ≥ 2 * log b / (log c + log a) := by
    have h121 : log (c + a) > 0 := by
      have h122 : c + a > 1 := by
        nlinarith
      have h123 : log (c + a) > 0 := by
        apply Real.log_pos
        all_goals linarith
      linarith
    have h124 : log c + log a > 0 := by
      linarith [h73, h71]
    have h125 : log (c + a) ≤ log c + log a := h43
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h72]

  have h111 : 2 * log c / (log a + log b) + 2 * log a / (log b + log c) + 2 * log b / (log c + log a) ≥ 3 := by
    have h1111 : 0 < log a := h71
    have h1112 : 0 < log b := h72
    have h1113 : 0 < log c := h73
    have h1114 : 2 * log c / (log a + log b) + 2 * log a / (log b + log c) + 2 * log b / (log c + log a) - 3 ≥ 0 := by
      have h1115 : 0 < (log a + log b) * (log b + log c) * (log c + log a) := by
        positivity
      have h1116 : (2 * log c / (log a + log b) + 2 * log a / (log b + log c) + 2 * log b / (log c + log a) - 3) =
          (2 * log c * (log b + log c) * (log c + log a) + 2 * log a * (log a + log b) * (log c + log a) + 2 * log b * (log a + log b) * (log b + log c) - 3 * (log a + log b) * (log b + log c) * (log c + log a)) / ((log a + log b) * (log b + log c) * (log c + log a)) := by
        field_simp
        ring
      rw [h1116]
      have h1117 : 2 * log c * (log b + log c) * (log c + log a) + 2 * log a * (log a + log b) * (log c + log a) + 2 * log b * (log a + log b) * (log b + log c) - 3 * (log a + log b) * (log b + log c) * (log c + log a) ≥ 0 := by
        have h1118 : 2 * log c * (log b + log c) * (log c + log a) + 2 * log a * (log a + log b) * (log c + log a) + 2 * log b * (log a + log b) * (log b + log c) - 3 * (log a + log b) * (log b + log c) * (log c + log a) = 
            (log a - log b)^2 * (log a + log b) + (log b - log c)^2 * (log b + log c) + (log c - log a)^2 * (log c + log a) := by
          nlinarith
        rw [h1118]
        have h1119 : (log a - log b)^2 * (log a + log b) + (log b - log c)^2 * (log b + log c) + (log c - log a)^2 * (log c + log a) ≥ 0 := by
          positivity
        linarith
      have h1118 : (2 * log c * (log b + log c) * (log c + log a) + 2 * log a * (log a + log b) * (log c + log a) + 2 * log b * (log a + log b) * (log b + log c) - 3 * (log a + log b) * (log b + log c) * (log c + log a)) / ((log a + log b) * (log b + log c) * (log c + log a)) ≥ 0 := by
        apply div_nonneg
        linarith
        positivity
      linarith
    linarith

  linarith [h31, h32, h33, h101, h102, h103, h111]