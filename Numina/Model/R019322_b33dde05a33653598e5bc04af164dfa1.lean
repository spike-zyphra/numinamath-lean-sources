import Mathlib

theorem algebra_2793 (x : ℝ) (hx : x = Real.pi) : Real.sqrt (x - Real.pi) + Real.sqrt (Real.pi - x) + (x - 1) / Real.pi = 1 - 1 / Real.pi := by
  have h1 : x - Real.pi = 0 := by 
    rw [hx]
    all_goals norm_num
  have h2 : Real.pi - x = 0 := by 
    rw [hx]
    all_goals norm_num
  have h3 : Real.sqrt (x - Real.pi) = 0 := by 
    rw [h1]
    simp
  have h4 : Real.sqrt (Real.pi - x) = 0 := by
    rw [h2]
    simp
  -- Now, we rewrite the terms in our goal.
  rw [h3, h4]
  rw [show x = Real.pi by linarith [hx]]
  -- Now we need to prove that expression for 1 - 1 / Real.pi
  have h7 : (Real.pi : ℝ ) ≠ (0 : ℝ ) := by 
    linarith [Real.pi_pos]
  field_simp [Real.pi_pos, h7]
  <;> ring_nf <;> linarith