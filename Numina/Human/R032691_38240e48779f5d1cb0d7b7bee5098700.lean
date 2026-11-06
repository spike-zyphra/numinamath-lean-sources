import Mathlib

theorem algebra_19511 (x : ℤ): (1 / 25 : ℝ) ^ (x + 2) = 125 ^ (-x) ↔ x = 4 := by
  constructor
  .
    -- Positive proof: Assuming the equation holds, derive x=4
    intro h
    -- Convert both sides of the equation to powers with a base of 5
    rw [show (1 / 25 : ℝ) = 5 ^ (-2 : ℤ)  by norm_num, 
        show (125 : ℝ) = 5 ^ (3: ℤ) by norm_num,← zpow_mul,← zpow_mul] at h
    ring_nf at h
    --Simplify the expression to obtain x=4
    rw [zpow_right_inj₀] at h
    linear_combination h
    --Ensure that the base of the power is greater than 0 and not 1
    linarith
    linarith
  .
    --Reverse proof: Assuming x=4, verify that the equation holds true
    intro h
    --Substitute and simplify
    rw [h]
    ring_nf
