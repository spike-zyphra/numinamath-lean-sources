import Mathlib

theorem number_theory_93358 (a b : ℕ) (ha : a > 0) (hb : b > 0)
(h : a * b = 161) (h' : Nat.ofDigits 10 [a, b] * Nat.ofDigits 10 [b, a] = 161) :
a * b = 224 := by
  have h1 : Nat.ofDigits 10 [a, b] = a + 10 * b := by 
    simp [Nat.ofDigits, List.foldl]
    all_goals omega
  have h2 : Nat.ofDigits 10 [b, a] = b + 10 * a := by 
    simp [Nat.ofDigits, List.foldl]
    all_goals omega

  rw [h1] at h'
  rw [h2] at h'
  have h3 : a ∣ 161 := by
    use b
    all_goals linarith
  have h4 : a ≤ 161 := by 
    exact Nat.le_of_dvd (by norm_num) h3
  interval_cases a <;> try { 
    omega
  }
  <;> norm_num at h h' ⊢
  <;> try { 
    nlinarith
  }