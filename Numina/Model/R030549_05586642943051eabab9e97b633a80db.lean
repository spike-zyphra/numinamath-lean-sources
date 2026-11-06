import Mathlib

theorem number_theory_172178 (a b c : ℕ) (ha : ¬ 3 ∣ a) (hb : ¬ 3 ∣ b) (hc : ¬ 3 ∣ c) :
    3 ∣ a + b + c ∨ 3 ∣ a + b ∨ 3 ∣ b + c ∨ 3 ∣ a + c := by
  have ha1 : a % 3 = 1 ∨ a % 3 = 2 := by 
    omega
  have hb1 : b % 3 = 1 ∨ b % 3 = 2 := by 
    omega
  have hc1 : c % 3 = 1 ∨ c % 3 = 2 := by 
    omega
  rcases ha1 with (ha1 | ha1) <;> rcases hb1 with (hb1 | hb1) <;> rcases hc1 with (hc1 | hc1) <;> simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ha1, hb1, hc1] at *
  <;> omega