import Mathlib

theorem algebra_227148 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) (hc : 0 ≤ c ∧ c ≤ 9)
    (h1 : a * (b + c) = 33) (h2 : b * (a + c) = 40) :
    100 * a + 10 * b + c = 347 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩ 
  interval_cases a <;> try { 
    omega 
  }
  <;> interval_cases b <;> try { 
    omega 
  }
  <;> interval_cases c <;> omega