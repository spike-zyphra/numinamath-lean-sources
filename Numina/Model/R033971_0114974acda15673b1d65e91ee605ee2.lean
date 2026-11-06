import Mathlib

open Real

theorem algebra_176740 : (1 / logb (1 / 2) (1 / 3)) + (1 / logb (1 / 5) (1 / 3)) ∈ Set.Ioo 2 3 := by
  have h1 : (1 / logb (1 / 2) (1 / 3)) + (1 / logb (1 / 5) (1 / 3)) = (log 10) / (log 3) := by
    have h2 : logb (1 / 2) (1 / 3) = log 3 / log 2 := by
      have h1 : logb (1 / 2) (1 / 3) = (log (1 / 3)) / (log (1 / 2)) := by
        field_simp [logb]
      have h2 : log (1 / 3) = - log 3 := by
        simp [log_div, log_one]
      have h3 : log (1 / 2) = - log 2 := by
        simp [log_div, log_one]
      rw [h1, h2, h3]
      <;> ring
    have h3 : logb (1 / 5) (1 / 3) = log 3 / log 5 := by
      have h4 : logb (1 / 5) (1 / 3) = (log (1 / 3)) / (log (1 / 5)) := by
        field_simp [logb]
      have h5 : log (1 / 3) = - log 3 := by
        simp [log_div, log_one]
      have h6 : log (1 / 5) = - log 5 := by
        simp [log_div, log_one]
      rw [h4, h5, h6]
      <;> ring
    calc
      (1 / logb (1 / 2) (1 / 3)) + (1 / logb (1 / 5) (1 / 3))
          = 1 / (log 3 / log 2) + 1 / (log 3 / log 5) := by rw [h2, h3]
      _ = (log 2 / log 3) + (log 5 / log 3) := by
        field_simp
      _ = (log 2 + log 5) / log 3 := by
        ring_nf
      _ = log (2 * 5) / log 3 := by
        rw [← log_mul (by norm_num) (by norm_num)]
      _ = log 10 / log 3 := by
        norm_num
  rw [h1]
  constructor
  · -- Show that 2 < (log 10) / (log 3)
    have h4 : 2 < (log 10) / (log 3) := by
      have h5 : log 3 > 0 := by
        apply log_pos
        all_goals linarith
      have h6 : 2 * log 3 < log 10 := by
        have h7 : log 9 = 2 * log 3 := by
          calc
            log 9 = log (3 ^ 2) := by norm_num
            _ = 2 * log 3 := by simp [log_pow]
        have h8 : log 9 < log 10 := by
          apply Real.log_lt_log
          all_goals norm_num
        linarith [h7, h8]
      have h8 : (log 10) / (log 3) > 2 := by
        apply (lt_div_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith
  · -- Show that (log 10) / (log 3) < 3
    have h7 : (log 10) / (log 3) < 3 := by
      have h5 : log 3 > 0 := by
        apply log_pos
        all_goals linarith
      have h6 : log 10 < 3 * log 3 := by
        have h7 : log 27 = 3 * log 3 := by
          calc
            log 27 = log (3 ^ 3) := by norm_num
            _ = 3 * log 3 := by simp [log_pow]
        have h8 : log 10 < log 27 := by
          apply Real.log_lt_log
          all_goals norm_num
        linarith [h7, h8]
      have h7' : (log 10) / (log 3) < 3 := by
        apply (div_lt_iff₀ (by linarith)).mpr
        linarith
      linarith
    linarith