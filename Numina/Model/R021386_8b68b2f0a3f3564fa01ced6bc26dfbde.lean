import Mathlib

theorem number_theory_108151 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hord : a < b ∧ b < c) (hrel : 13 * a + 65 * b + 289 * c = 6622) :
    a = 2 ∧ b = 17 ∧ c = 19 := by 
  have h1 : a < b := hord.1
  have h2 : b < c := hord.2
  have h3 : a ≤ 509 := by 
    omega
  have h4 : b ≤ 102 := by
    omega
  have h5 : c ≤ 23 := by
    omega
  interval_cases c <;> try { 
    omega
  } <;> interval_cases b <;> try { 
    omega
  } <;> interval_cases a <;> try { 
    omega
  } <;> norm_num at hrel ha hb hc h1 h2
    <;> try { contradiction }
    <;> tauto