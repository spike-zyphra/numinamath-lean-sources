import Mathlib

theorem number_theory_242229 : ¬∃ p n, p.Prime ∧ p ∣ 91 ∧ p = 8 * n + 3 := by 
  rintro ⟨p, n, hp, h1, h2⟩
  have h3 : p ≤ 91 := by
    exact Nat.le_of_dvd (by norm_num) h1
  interval_cases p <;> norm_num at hp h1 h2 <;> try { 
    omega 
  } <;> contradiction