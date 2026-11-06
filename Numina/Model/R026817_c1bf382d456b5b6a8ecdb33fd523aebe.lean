import Mathlib

theorem number_theory_223558 (a b c d : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d)
    (h6 : c ≠ d) (h7 : a < 10) (h8 : b < 10) (h9 : c < 10) (h10 : d < 10)
    (h11 : a * b = 24) (h12 : c * d = 30) :
    a + b + c + d = 22 := by
  have h13 : a ≤ 9 := by linarith
  have h14 : b ≤ 9 := by linarith
  have h15 : c ≤ 9 := by linarith
  have h16 : d ≤ 9 := by linarith
  interval_cases a <;> interval_cases b <;> try { omega }
  <;> interval_cases c <;> interval_cases d <;> try { omega }
  <;> try { tauto }