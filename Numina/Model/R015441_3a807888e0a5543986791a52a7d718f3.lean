import Mathlib

theorem algebra_114521 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b - a - b = 12) :
    (a, b) = (2, 14) ∨ (a, b) = (14, 2) := by
  have h1 : a * b = a + b + 12 := by
    omega
  have h2 : a ≤ 15 := by
    by_contra h2
    push_neg at h2
    have h4 : b ≤ 15 := by
      nlinarith [h1, h2, mul_pos ha hb]
    interval_cases b <;> try { 
      omega 
    } 
    <;> nlinarith
  have h3 : b ≤ 15 := by
    by_contra h3
    push_neg at h3
    have h4 : a ≤ 15 := by
      nlinarith [h1, h3, mul_pos ha hb]
    interval_cases a <;> try { 
      omega 
    } 
    <;> nlinarith
  interval_cases a <;> interval_cases b <;> norm_num [Prod.ext_iff] at h ⊢ <;> omega
  <;> norm_num [Prod.ext_iff] at h ⊢ <;> omega
  all_goals omega
  <;> norm_num [Prod.ext_iff] at h ⊢ <;> omega
  <;> norm_num [Prod.ext_iff] at h ⊢ <;> omega
  all_goals try omega