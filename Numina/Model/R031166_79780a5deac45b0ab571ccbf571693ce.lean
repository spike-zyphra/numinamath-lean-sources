import Mathlib

/- If $a$, $b$, $c$ are all prime numbers, and $b+c=13$, ${c}^{2}-{a}^{2}=72$, then $a+b+c=$ ___          ___. -/
theorem number_theory_1288
    (a b c : ℕ)
    (ha : a.Prime)
    (hb : b.Prime)
    (hc : c.Prime)
    (h1 : b + c = 13)
    (h2 : c^2 - a^2 = 72) :
    a + b + c = 20 := by
  have h3 : b ≤ 13 := by
    omega
  have h4 : c ≤ 13 := by
    omega
  have h5 : a ≤ 16 := by 
    by_contra h
    push_neg at h 
    -- a >= 17
    have h6 : a ≥ 17 := by linarith
    -- c <= 13
    have h7 : c ≤ 13 := by nlinarith
    have h8 : c^2 ≤ 169 := by 
      nlinarith
    have h9 : c^2 - a^2 = 72 := by
      omega
    have h10 : c^2 = a^2 + 72 := by 
      omega
    nlinarith
  interval_cases b <;> interval_cases c 
  <;> norm_num at h1 h2 hb hc 
  <;> try { 
    have h5' : a ≤ 16 := h5 
    interval_cases a <;> norm_num at h2 ha 
    <;> omega 
  }
  <;> try { 
    all_goals 
    exfalso 
    <;> try { 
      contradiction 
    } 
    <;> try { 
      nlinarith 
    }
  }
  <;> try { 
    all_goals 
    omega 
  }