import Mathlib

theorem number_theory_98497 (a b c d : ℕ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (h1 : 0 < a) (h2 : 0 < b) (h3 : 0 < c) (h4 : 0 < d)
    (h5 : a < 10) (h6 : b < 10) (h7 : c < 10) (h8 : d < 10) (h9 : a * b = 24) (h10 : c * d = 30) :
    a + b + c + d = 22 := by
  have h11 : a ≤ 9 := by linarith
  have h12 : b ≤ 9 := by linarith
  have h13 : c ≤ 9 := by linarith
  have h14 : d ≤ 9 := by linarith
  interval_cases a <;> try { omega }
  <;> try { interval_cases b <;> omega }
  <;> try { interval_cases c <;> omega }
  <;> try { interval_cases d <;> omega }