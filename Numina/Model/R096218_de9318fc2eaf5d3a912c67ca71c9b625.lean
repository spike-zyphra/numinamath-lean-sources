import Mathlib

theorem number_theory_242101 {a b : ℕ} (ha : a = 18) (hb : b = 1) :
    a > 0 ∧ b > 0 ∧ ¬(7 ∣ a * b * (a + b)) ∧ 7^7 ∣ (a + b)^7 - a^7 - b^7 := by 
  subst ha 
  subst hb 
  repeat { constructor }
  all_goals 
    norm_num
  all_goals 
    native_decide