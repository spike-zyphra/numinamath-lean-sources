import Mathlib

theorem number_theory_43513 {a b : ℕ} (ha : a = 2^12) (hb : b = 2^9) :
    0 < a ∧ 0 < b ∧ a ∣ b^2 ∧ b^2 ∣ a^3 ∧ a^3 ∣ b^4 ∧ b^4 ∣ a^5 ∧ ¬a^5 ∣ b^6 := by
  rw [ha, hb]
  repeat { constructor }
  all_goals norm_num