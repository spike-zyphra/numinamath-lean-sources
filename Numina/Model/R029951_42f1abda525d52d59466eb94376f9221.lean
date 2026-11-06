import Mathlib

open Real

theorem inequalities_85141 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (hab : a ≠ b) : logb a (logb a b) > logb b (logb a b) := by 
  have h3 : 0 < a := by linarith
  have h4 : 0 < b := by linarith
  have h6 : logb a b = log b / log a := by 
    field_simp [logb]
  have h7 : logb a (logb a b) = (log (log b / log a) ) / log a := by
    rw [h6]
    field_simp [logb]
  have h8 : logb b (logb a b) = (log (log b / log a) ) / log b := by 
    rw [h6]
    field_simp [logb]
  have h9 : log a > 0 := by
    apply log_pos
    linarith
  have h10 : log b > 0 := by
    apply log_pos
    linarith
  have h7' : logb a (logb a b) - logb b (logb a b) > 0 := by
    rw [h7, h8]
    have h15 : log (log b / log a) = (log (log b) - log (log a) ) := by 
      rw [log_div (by positivity) (by positivity)]
    have h18 : (log (log b / log a) ) / log a - (log (log b / log a) ) / log b = 
      (log (log b / log a) ) * ( (log b - log a) / (log a * log b) ) := by 
      field_simp
      <;> ring_nf 
    have h19 : (log (log b / log a) ) * ( (log b - log a) / (log a * log b) ) > 0 := by
      have h20 : log a > 0 := h9
      have h21 : log b > 0 := h10
      by_cases h22 : log b > log a 
      · -- Since 0 < log a < log b
        have h23 : log (log b) > log (log a) := by 
          apply log_lt_log 
          all_goals nlinarith 
        have h24 : log (log b / log a) > 0 := by
          have h25 : log (log b / log a) = log (log b) - log (log a) := by 
            rw [log_div (by positivity) (by positivity)]
          rw [h25]
          linarith 
        have h26 : (log b - log a) / (log a * log b) > 0 := by 
          apply div_pos 
          · linarith 
          · positivity 
        positivity 
      by_cases h22 : log b < log a 
      · -- $\log b < \log a$
        have h23 : log (log b) < log (log a) := by 
          apply log_lt_log 
          all_goals nlinarith 
        have h24 : log (log b / log a) < 0 := by 
          have h25 : log (log b / log a) = log (log b) - log (log a) := by 
            rw [log_div (by positivity) (by positivity)]
          rw [h25]
          linarith 
        have h26 : (log b - log a) / (log a * log b) < 0 := by 
          apply div_neg_of_neg_of_pos 
          · linarith 
          · positivity 
        have h28 : (log (log b / log a) ) * ( (log b - log a) / (log a * log b) ) > 0 := by 
          nlinarith 
        linarith 
      · -- $\log b = \log a$
        have h26 : log b = log a := by linarith 
        have h27 : b = a := by 
          exact log_injOn_pos (Set.mem_Ioi.mpr h4) (Set.mem_Ioi.mpr h3) h26 
        have h28 : a = b := by 
          linarith 
        have h29 : a ≠ b := hab 
        contradiction 
    linarith 
  linarith