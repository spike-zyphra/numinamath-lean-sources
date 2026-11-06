import Mathlib

theorem number_theory_264693 (m n : ℕ) (hm : 2 * m + 2 * (Nat.digits 10 n).sum = 70) (hn : n * (Nat.digits 10 m).sum = 70) :
    (m, n) = (34, 10) ∨ (m, n) = (28, 7) := by
  have h1 : m + (Nat.digits 10 n).sum = 35 := by
    omega
  have h2 : n ∣ 70 := by
    use (Nat.digits 10 m).sum
    all_goals linarith
  have h3 : n ≤ 70 := by
    exact Nat.le_of_dvd (by omega) h2
  interval_cases n <;> norm_num at hn h1 ⊢
  <;> norm_num [Prod.ext_iff] at *
  <;> try { 
    omega 
  }
  <;> try { 
    all_goals 
    have h4 : m ≤ 35 := by 
      omega 
    interval_cases m <;> norm_num at h1 hn ⊢ 
    <;> tauto 
  }