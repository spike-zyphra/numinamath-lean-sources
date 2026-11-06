import Mathlib

theorem algebra_66455 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b * c = 2010) (h2 : b + c * a = 250) :
    (a, b, c) = (3, 223, 9) := by
  have h3 : (b - a) * (c - 1) = 1760 := by
    nlinarith 
  have ha1 : a ≥ 1 := by omega
  have hb1 : b ≥ 1 := by omega
  have h4 : c ≤ 249 := by
    nlinarith [h2, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  interval_cases c <;> norm_num [Prod.ext_iff] at h1 h2 ⊢ 
    <;> omega