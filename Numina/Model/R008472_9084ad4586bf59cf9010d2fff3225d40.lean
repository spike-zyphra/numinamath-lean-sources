import Mathlib

/-Let a_n=6^n+8^n. Determine the remainder upon dividing 49-/

def a (n : ℕ) := 6 ^ n + 8 ^ n

theorem AIME_Number_Theory_94473 : a 83 % 49 = 35 := by
  norm_num [a]