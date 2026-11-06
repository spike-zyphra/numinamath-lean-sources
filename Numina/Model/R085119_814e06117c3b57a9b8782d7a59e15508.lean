import Mathlib

theorem number_theory_3306 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
(hc : 0 ≤ c ∧ c ≤ 9) (h : c * (b * 10 + c) * (a * 100 + b * 10 + c) = 11904) :
a * 100 + b * 10 + c = 124 := by
  have ha1 : 1 ≤ a := ha.1
  have ha2 : a ≤ 9 := ha.2
  have hb1 : 0 ≤ b := hb.1
  have hb2 : b ≤ 9 := hb.2
  have hc1 : 0 ≤ c := hc.1
  have hc2 : c ≤ 9 := hc.2
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega