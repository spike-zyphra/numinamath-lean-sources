import Mathlib

theorem number_theory_251997 {a b : ℕ} (ha : a = 1) (hb : b = 18) :
    ¬(7 ∣ a) ∧ ¬(7 ∣ b) ∧ ¬(7 ∣ a + b) ∧ 7^7 ∣ (a + b)^7 - a^7 - b^7 := by 
  rw [ha, hb]
  constructor
  · -- Show that 7 does not divide 1
    norm_num
  constructor
  · -- Show that 7 does not divide 18
    norm_num
  constructor
  · -- Show that 7 does not divide 19
    norm_num
  · -- Show divisibility
    norm_num