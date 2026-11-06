import Mathlib

theorem number_theory_13944 : (Nat.floor ((10^2016 : ℝ) / (10^672 + 2015)) % 10000000 = 4060224) := by
  have h1 : Nat.floor ((10^2016 : ℝ) / (10^672 + 2015)) = (10^2016) / (10^672 + 2015) := by
    norm_num [Nat.floor_eq_iff]
  rw [h1]
  norm_num
  <;> native_decide