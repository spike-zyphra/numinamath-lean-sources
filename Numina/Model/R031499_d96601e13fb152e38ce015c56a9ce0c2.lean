import Mathlib

theorem number_theory_101808 {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsum : a + b = 29) (hdiv : a.divisors.card = 2) (hdiv' : b.divisors.card = 5)
    (hsum' : ∑ d ∈ a.divisors, d + ∑ d ∈ b.divisors, d = 45) :
    a = 13 ∧ b = 16 := by
  have h2 : b = 29 - a := by 
    omega 
  have ha1 : a > 0 := by
    by_contra h
    push_neg at h 
    have ha0 : a = 0 := by 
      omega 
    contradiction 
  have ha1 : a > 0 := ha1
  have ha2 : a ≤ 28 := by
    by_contra h 
    push_neg at h 
    have ha2 : a ≥ 29 := by 
      omega 
    have h3 : b = 0 := by 
      omega 
    contradiction 
  interval_cases a <;> simp [h2] at *
  <;> try { contradiction }
  <;> omega