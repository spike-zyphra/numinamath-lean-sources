import Mathlib

theorem number_theory_322313 :
    Set.ncard {n : ℕ | ∃ k, k^2 = n^2 + 5 * n + 13} = 1 := by
  have h1 : {n : ℕ | ∃ k, k^2 = n^2 + 5 * n + 13} = {4} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Forward: if $n$ is in the set, then $n=4$
      intro h
      rcases h with ⟨k, hk⟩
      have h2 : (2 * k : ℤ)^2 - (2 * (n : ℤ) + 5)^2 = 27 := by
        nlinarith
      have h5 : ((2 * k : ℤ) - (2 * (n : ℤ) + 5)) * ((2 * k : ℤ) + (2 * (n : ℤ) + 5)) = 27 := by
        nlinarith
      have h6 : (2 * k : ℤ) - (2 * (n : ℤ) + 5) ∣ 27 := by
        use ((2 * k : ℤ) + (2 * (n : ℤ) + 5))
        all_goals nlinarith
      have h7 : (2 * k : ℤ) - (2 * (n : ℤ) + 5) ≤ 27 := by
        apply Int.le_of_dvd (by norm_num) h6
      have h8 : (2 * k : ℤ) - (2 * (n : ℤ) + 5) ≥ -27 := by
        have h9 : (- ((2 * k : ℤ) - (2 * (n : ℤ) + 5)) ) ∣ 27 := by
          exact Int.neg_dvd.2 h6
        have h10 : - ((2 * k : ℤ) - (2 * (n : ℤ) + 5)) ≤ 27 := by
          apply Int.le_of_dvd (by norm_num) h9
        linarith
      interval_cases h : (2 * k : ℤ) - (2 * (n : ℤ) + 5) <;> omega
    · -- Backward: if n=4, then it is in the set
      intro h
      rw [h]
      use 7
      all_goals norm_num
  rw [h1]
  simp