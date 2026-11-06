import Mathlib

theorem number_theory_217228 : ⌊(10^93 / (10^31 + 3 : ℝ))⌋ % 100 = 8 := by
  have h1 : ⌊(10^93 / (10^31 + 3 : ℝ))⌋ = (10^93) / (10^31 + 3) := by
    norm_num
    <;> omega
  rw [h1]
  norm_num