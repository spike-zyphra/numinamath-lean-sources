import Mathlib

theorem algebra_150396 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a^3 - b^3 - c^3 = 3*a*b*c) (h2 : a^2 = 2*(a + b + c)) :
    (a = 4 ∧ b = 1 ∧ c = 3) ∨ (a = 4 ∧ b = 2 ∧ c = 2) ∨ (a = 4 ∧ b = 3 ∧ c = 1) := by
  have h3 : a = b + c := by
    have h4 : a^3 - b^3 - c^3 - 3 * a * b * c = 0 := by
      linarith 
    have h5 : (a - b - c) * (a^2 + b^2 + c^2 + a * b + a * c - b * c) = 0 := by
      ring_nf at h4 ⊢
      nlinarith
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- When `a - b - c = 0`
      linarith
    · -- When `a^2 + b^2 + c^2 + ab + ac - b*c = 0`
      have h8 : (a + b)^2 + (a + c)^2 + (b - c)^2 = 0 := by
        nlinarith [h7]
      have h9 : (a + b)^2 ≥ 0 := by nlinarith
      have h10 : (a + c)^2 ≥ 0 := by nlinarith
      have h11 : (b - c)^2 ≥ 0 := by nlinarith
      have h12 : (a + b)^2 = 0 := by nlinarith
      have h13 : (a + c)^2 = 0 := by nlinarith
      have h14 : (b - c)^2 = 0 := by nlinarith
      have h15 : a + b = 0 := by
        nlinarith [h12]
      have h16 : a + c = 0 := by
        nlinarith [h13]
      nlinarith [h15, h16, ha, hb, hc]
  have h4 : a = 4 := by 
    have h5 : a^2 = 2 * (a + b + c) := h2
    have h6 : a = b + c := h3
    rw [show a = b + c by linarith [h6]] at h5 
    have h7 : (b + c) * (b + c - 4) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case `b + c = 0`, which contradicts `b > 0` and `c > 0`.
      nlinarith [hb, hc]
    · -- Case `b + c - 4 = 0`, so `b + c = 4`.
      have h10 : b + c = 4 := by linarith 
      have ha4 : a = 4 := by linarith [h10, h6]
      exact ha4
  have h10 : b + c = 4 := by 
    linarith [h3, h4]
  have h11 : b ≤ 3 := by 
    nlinarith [h10, hb, hc]
  have h12 : b ≥ 1 := by 
    linarith [hb]
  have h13 : c = 4 - b := by 
    linarith [h10]
  interval_cases b <;> try { 
    omega 
  } <;> try { 
    norm_num [h4, h13] at *
    all_goals 
    try { 
      tauto 
    }
    <;> try { 
      nlinarith 
    }
  }