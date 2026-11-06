import Mathlib

theorem number_theory_95042 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 9 ∣ (500 + 10 * b + 9) ∧ (500 + 10 * b + 9) = 326 + (200 + 10 * a + 3)) :
    a + b = 6 := by 
  rcases h with ⟨h1, h2⟩ 
  omega