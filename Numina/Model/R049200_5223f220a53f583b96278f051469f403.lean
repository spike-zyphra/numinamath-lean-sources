import Mathlib

theorem number_theory_240836 {a b c : ℕ} (ha : a = 1666667) (hb : b = 3333334)
    (hc : c = 16666673333334) :
    a * b = c / 3 := by 
  subst ha
  subst hb
  subst hc
  all_goals norm_num