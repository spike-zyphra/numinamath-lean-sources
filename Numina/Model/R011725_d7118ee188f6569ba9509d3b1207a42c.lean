import Mathlib

theorem number_theory_288078 (m n : ℕ)
  (hm : m > 0) (hn : n > 0) (hmn : m * n = 5000)
  (hdiv : ¬(10 ∣ m) ∧ ¬(10 ∣ n)) : m + n = 633 :=
by
  rcases hdiv with ⟨hm10, hn10⟩
  have h1 : m ∣ 5000 := by 
    use n 
    all_goals linarith 
  have h2 : n ∣ 5000 := by 
    use m 
    all_goals linarith
  have h3 : m ≤ 5000 := by
    exact Nat.le_of_dvd (by linarith) h1 
  by_cases h : m > 70 
  · -- m > 70 
    have h4 : n ≤ 71 := by 
      nlinarith [hmn, h] 
    interval_cases n <;> norm_num at hmn hn10 ⊢ 
    <;> try { 
      omega 
    }
  · -- m ≤ 70 
    have h5 : m ≤ 70 := by linarith 
    interval_cases m <;> norm_num at hmn hm10 ⊢ 
    <;> try { 
      omega 
    }