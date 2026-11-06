import Mathlib

theorem number_theory_5337 {a b : ℕ} (ha : a = 0b110100111) (hb : b = 0b11101) :
    a / b = 0b1110 ∧ a % b = 0b10001 := by 
  subst ha
  subst hb
  all_goals
    norm_num