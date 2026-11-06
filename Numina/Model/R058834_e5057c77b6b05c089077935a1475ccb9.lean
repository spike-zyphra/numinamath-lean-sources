import Mathlib

theorem number_theory_201169 (a : Fin 6 → ℕ) (ha : a = ![0, 3, 7, 11, 19, 20]) :
    a 0 < a 1 ∧ a 1 < a 2 ∧ a 2 < a 3 ∧ a 3 < a 4 ∧ a 4 < a 5 := by
  simp [ha]
  <;> try { all_goals trivial }
  all_goals try { omega }