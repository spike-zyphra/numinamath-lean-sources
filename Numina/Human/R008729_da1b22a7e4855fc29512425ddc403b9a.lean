import Mathlib

/- The average American consumes 1483 pounds of candy in a lifetime. Assuming that 1 year $=$ 52 weeks and the average life-span is 75 years, how many pounds of candy per week does the average American consume? Express your answer as a decimal to the nearest hundredth. -/
theorem algebra_21088 (c : ℝ) (hc : c = 1483) : round (((c / 75) / 52) * 10 ^ 2) = 38 := by
  rw [hc]
  dsimp [round]
  norm_num
  -- suffices to show that the fraction part of $1483 / 39$ is less than $0.5$
  have nle : ¬1 ≤ 2 * Int.fract (1483 / 39 : ℝ) := by
    simp only [not_le]
    show 2 * Int.fract ((1483 : ℤ) / (39 : ℕ) : ℝ) < 1
    rw [Int.fract_div_intCast_eq_div_intCast_mod]
    norm_num
  aesop
