import Mathlib

theorem number_theory_219502 {a b c : ℤ} (ha : a = 80) (hb : b = 320) (hc : c = 41) :
    IsSquare (a + b + c) ∧ IsSquare (a + b) ∧ IsSquare (a + c) ∧ IsSquare (b + c) := by
  rw [ha, hb, hc]
  constructor
  · -- Show that 441 is square
    use 21
    all_goals norm_num
  constructor
  · -- Show that 400 is square
    use 20
    all_goals norm_num
  constructor
  · -- Show that 121 is square
    use 11
    all_goals norm_num
  · -- Show that 361 is square
    use 19
    all_goals norm_num