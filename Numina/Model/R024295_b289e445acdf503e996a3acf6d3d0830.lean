import Mathlib

open Real

theorem inequalities_158190 {x : ℝ} (hx : 0 < x) : exp x > 1 + log (1 + x) := by
  have h11 : exp x > 1 + x := by 
    have h41 : x > 0 := hx
    have h42 : exp x > 1 + x := by
      have h43 : x > (0 : ℝ) := h41 
      -- We can derive this from `exp x - (1 + x) > 0` for x > 0
      -- This standard library fact on strict convexity
      have h44 : x ≠ 0 := by linarith 
      have h45 : exp x > 1 + x := by 
        -- From `add_one_lt_exp` in Mathlib4.
        -- The theorem is `exp y > 1 + y` for `y ≠ 0`.
        have h46 : x + 1 < exp x := by 
          apply Real.add_one_lt_exp 
          simpa using h44 
        have h47 : (1 + x) = (x + 1) := by linarith 
        rw [h47] at * 
        linarith 
      linarith 
    linarith 
  have h3 : log (1 + x) < x := by 
    have h4 : x > 0 := hx 
    have h5 : log (1 + x) < x := by 
      have h8 : log (1 + x) < x := by
        have h9 : log (1 + x) < (1 + x) - 1 := by 
          apply Real.log_lt_sub_one_of_pos 
          all_goals nlinarith 
        have h10 : (1 + x) - 1 = x := by linarith 
        linarith [h10, h9] 
      linarith 
    linarith 
  linarith [h11, h3]