import Mathlib



theorem number_theory_65953 {n : ℕ} (hn : n > 0) {S : ℕ → ℕ} 
    (hs : S = fun n => (Nat.digits 10 n).sum) :
    n * (S n - 1) = 2010 ↔ n = 402 := by
  constructor
  · -- Forward: if $n \cdot (S n - 1) = 2010$, then $n = 402$.
    intro h_eq
    have h1 : n ∣ 2010 := by 
      use S n - 1
      all_goals
      omega
    have h3 : n ≤ 2010 := by 
      exact Nat.le_of_dvd (by linarith) h1
    by_cases h4 : n ≤ 670
    · 
      interval_cases n <;> norm_num [hs] at h_eq ⊢ 
      <;> omega 
    · -- Case where n > 670
      have h5 : n > 670 := by 
        omega 
      have h6 : n ≤ 2010 := by
        exact Nat.le_of_dvd (by linarith) h1
      have : n = 1005 ∨ n = 2010 := by
        interval_cases n <;> norm_num at h1 ⊢
        <;> try { tauto }
        all_goals 
          omega 
      rcases this with (r | r)
      · -- n = 1005
        rw [r] at h_eq 
        norm_num [hs] at h_eq 
        all_goals 
          omega 
      · -- n = 2010
        rw [r] at h_eq 
        norm_num [hs] at h_eq 
        all_goals 
          omega 
  · -- Backward: if n = 402, then $n \cdot (S n - 1) = 2010$.
    intro h_eq
    rw [h_eq]
    norm_num [hs]
    <;> omega