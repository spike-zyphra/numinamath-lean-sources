import Mathlib

theorem number_theory_150057 (a : Fin 9 → ℕ) (ha : a = ![3, 1, 7, 4, 9, 2, 6, 5, 8]) :
    ∀ i, ¬(3 ∣ a i + a ((i + 1) % 9)) ∧ ¬(5 ∣ a i + a ((i + 1) % 9)) ∧ ¬(7 ∣ a i + a ((i + 1) % 9)) := by
  intro i
  rw [ha]
  fin_cases i <;> simp at *
  <;> repeat { 
    constructor
    all_goals try { 
      native_decide
    }
  }
  <;> try { 
    native_decide
  }