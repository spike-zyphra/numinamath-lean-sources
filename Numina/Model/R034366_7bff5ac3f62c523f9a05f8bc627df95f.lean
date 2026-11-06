import Mathlib

open Real

theorem algebra_126559 {x : ℝ} (hx : x > 1) :
    x^(log (log x)) - (log x)^(log x) = 0 := by
  have h2 : log x > 0 := by
    apply log_pos
    linarith
  have h3 : x ^ (log (log x)) = (log x) ^ (log x) := by
    have h4 : log (x ^ (log (log x))) = log ((log x) ^ (log x)) := by
      have h5 : log (x ^ (log (log x))) = log (log x) * log x := by 
        rw [log_rpow]
        all_goals
          linarith
      have h6 : log ((log x) ^ (log x)) = log x * log (log x) := by 
        rw [log_rpow]
        all_goals
          have h7 : log x > 0 := h2
          all_goals
            linarith
      rw [h5, h6]
      <;> ring
    have h8 : x ^ (log (log x)) > 0 := by 
      positivity
    have h9 : (log x) ^ (log x) > 0 := by 
      positivity
    have h11 : x ^ (log (log x)) = (log x) ^ (log x) := by
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h8) (Set.mem_Ioi.mpr h9) h4
    exact h11
  linarith [h3]