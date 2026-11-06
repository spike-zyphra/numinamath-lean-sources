import Mathlib

theorem number_theory_23074 (a b c : ℤ) (ha : 0 < a ∧ a < 13) (hb : 0 < b ∧ b < 13) (hc : 0 < c ∧ c < 13)
    (h1 : 2*a*b+b*c+c*a ≡ 0 [ZMOD 13]) (h2 : a*b+2*b*c+c*a ≡ 6*a*b*c [ZMOD 13]) (h3 : a*b+b*c+2*c*a ≡ 8*a*b*c [ZMOD 13]) :
    a+b+c ≡ 5 [ZMOD 13] := by 
  norm_num [Int.ModEq] at h1 h2 h3 ⊢
  have ha1 : a > 0 := ha.1
  have ha2 : a < 13 := ha.2
  have hb1 : b > 0 := hb.1
  have hb2 : b < 13 := hb.2
  have hc1 : c > 0 := hc.1
  have hc2 : c < 13 := hc.2
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega