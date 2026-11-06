import Mathlib

theorem algebra_36142 {c d : ℕ} (hcd : c > 1 ∧ c < 10) (hfd : 6 * c * d = 6 * 91) :
    c + d = 20 := by
  have h1 : c * d = 91 := by
    nlinarith
  have h2 : c < 10 := hcd.right
  have h3 : c > 1 := hcd.left
  interval_cases c <;> try { 
    omega 
  } <;> try { 
    all_goals 
    have h4 : d ≤ 91 := by
      nlinarith
    interval_cases d <;> omega 
  }