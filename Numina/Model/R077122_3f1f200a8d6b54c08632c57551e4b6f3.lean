import Mathlib

theorem number_theory_223585 (a b c : ℕ) (ha : ¬ 5 ∣ a) (hb : ¬ 5 ∣ b) (hc : ¬ 5 ∣ c) :
    5 ∣ (a^2 - b^2) ∨ 5 ∣ (b^2 - c^2) ∨ 5 ∣ (c^2 - a^2) := by
  have ha2 : a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by 
    omega
  have hb2 : b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by 
    omega
  have hc2 : c % 5 = 1 ∨ c % 5 = 2 ∨ c % 5 = 3 ∨ c % 5 = 4 := by 
    omega
  have ha2' : a^2 % 5 = 1 ∨ a^2 % 5 = 4 := by 
    rcases ha2 with (h | h | h | h) <;> 
      ( norm_num [Nat.pow_mod, h] <;> omega )
  have hb2' : b^2 % 5 = 1 ∨ b^2 % 5 = 4 := by 
    rcases hb2 with (h | h | h | h) <;> 
      ( norm_num [Nat.pow_mod, h] <;> omega )
  have hc2' : c^2 % 5 = 1 ∨ c^2 % 5 = 4 := by 
    rcases hc2 with (h | h | h | h) <;> 
      ( norm_num [Nat.pow_mod, h] <;> omega )
  omega