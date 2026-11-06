import Mathlib

theorem number_theory_7883 (a b c d : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9)
    (hc : 0 ≤ c ∧ c ≤ 9) (hd : 0 ≤ d ∧ d ≤ 9) (h : 1000 * a + 100 * b + 10 * c + d =
    a ^ a + b ^ b + c ^ c + d ^ d) : a = 3 := by
  have h1 : a ≤ 9 := by linarith [ha.2]
  have h2 : b ≤ 9 := by linarith [hb.2]
  have h3 : c ≤ 9 := by linarith [hc.2]
  have h4 : d ≤ 9 := by linarith [hd.2]
  have ha1 : a ≥ 1 := by linarith [ha.1]
  interval_cases a <;> try { 
    omega
  }
  <;> interval_cases b <;> try { 
    omega 
  }
  <;> interval_cases c <;> interval_cases d 
  <;> norm_num [Nat.pow_succ] at h 
  <;> omega