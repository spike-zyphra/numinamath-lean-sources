import Mathlib

theorem number_theory_223274 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a > b ∧ b > c ∧ c > 1) (h' : a * b * c = 105) :
    a = 7 := by
  rcases h with ⟨ha1, hb1, hc1⟩ 
  -- From c > 1, so c ≥ 2.
  have hc2 : c ≥ 2 := by linarith 
  -- Establish h1: a * b * c = 105.
  have h1 : a * b * c = 105 := h'
  -- Derive a * b \le 52 because c \geq 2
  have h2 : a * b ≤ 52 := by
    have h5 : c ≥ 2 := hc2 
    have h6 : a * b * c = 105 := h1
    nlinarith [h1, h5]
  -- Derive bound for a as ≤52
  have ha2 : a ≤ 52 := by 
    nlinarith [show b ≥ 1 by omega, h2]
  -- Derive bound for b as ≤52
  have hb2 : b ≤ 52 := by 
    nlinarith [show a ≥ 1 by omega, h2]
  -- Use exhaustive search over a and b, which are bounded.
  interval_cases a <;> try { 
    omega 
  }
  <;> try { 
    interval_cases b <;> try { 
      omega 
    }
  }