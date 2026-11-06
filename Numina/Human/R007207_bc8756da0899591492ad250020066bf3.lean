import Mathlib

open Classical

/- While Steve and LeRoy are fishing 1 mile from shore, their boat springs a leak, and water comes in at a constant rate of 10 gallons per minute. The boat will sink if it takes in more than 30 gallons of water. Steve starts rowing towards the shore at a constant rate of 4 miles per hour while LeRoy bails water out of the boat. What is the slowest rate, in gallons per minute, at which LeRoy can bail if they are to reach the shore without sinking? -/

theorem amc_algebra_1193 (x : ℚ) (h : (10 - x) * (60 / 4) <= 30) : (x >= 8) := by
  /- Arithmetic simplifications. -/
  /- Solve fractions. -/
  norm_num at h  
  have h₁ := (le_div_iff₀ (by decide)).mpr h
  /- Move multiplicative constants to RHS. Solve. -/
  have h₂ := neg_le_neg_iff.mpr h₁
  norm_num at h₂
  /- Rearrange additively. -/
  have h₃ : x >= 8 := by linarith
  exact h₃