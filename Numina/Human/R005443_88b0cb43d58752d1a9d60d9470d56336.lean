import Mathlib

/-
Problem :
This is a variant of the classic Monty Hall problem.
-/
theorem Combinatorics_608318
    (total_doors prize_doors host_opens prizes_opened : ℕ) 
    (h_total : total_doors = 7)            -- Total number of doors
    (h_prize : prize_doors = 2)          -- Number of doors hiding prizes
    (h_opens : host_opens = 3)            -- Number of doors opened by the host
    (h_prizes_opened : prizes_opened = 1) -- Number of prizes revealed by the host
    (switch_success : P = ((total_doors - prize_doors) : ℝ) / (total_doors : ℝ) * (prize_doors - prizes_opened : ℝ) / (total_doors - 1 - host_opens : ℝ)) :
    P = (5 / 21 : ℝ) := by

  -- Substitute known values into the probability formula
  rw [h_total, h_prize, h_opens] at switch_success
  
  -- Compute numerical values using the remaining hypothesis
  norm_num [h_prizes_opened] at switch_success
  
  -- Solve the resulting linear arithmetic equality
  linarith