import Mathlib

theorem number_theory_158062 : ∃ n > 0, (Nat.digits 10 n).all (fun d => d = 1) ∧ 2019 ∣ n := by 
  use ((10 ^ 672 - 1) / 9)
  constructor 
  · -- Show that n is positive
    norm_num 
  constructor 
  · -- Show that all digits of n are 1
    native_decide
  · -- Show that 2019 divides n
    native_decide