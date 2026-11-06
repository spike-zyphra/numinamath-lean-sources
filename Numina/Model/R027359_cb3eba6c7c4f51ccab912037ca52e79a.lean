import Mathlib

theorem algebra_1648 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h1 : a > b) (h2 : a * b = 2 * (2 * a + 2 * b)) :
    a + b = 25 ∨ a + b = 18 := by
  have h3 : b ≤ 7 := by
    by_contra h
    push_neg at h
    have h4 : a ≤ 8 := by
      nlinarith
    have h5 : a > b := h1
    have h6 : b ≥ 8 := by
      omega
    have h7 : a > 8 := by
      nlinarith
    all_goals nlinarith
  interval_cases b <;> try { 
    omega 
  } <;> try { 
    have h7 : a ≤ 24 := by
      nlinarith
    interval_cases a <;> omega 
  }