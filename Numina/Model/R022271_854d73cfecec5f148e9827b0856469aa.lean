import Mathlib

theorem number_theory_52248 :
    IsGreatest {k | ∃ n, 3^11 = ∑ i ∈ Finset.range k, (n + i)} 486 := by
  constructor
  · -- Show that 486 is in the set
    use 122
    native_decide
  · -- Show that 486 is greatest in the set
    intro k hk
    rcases hk with ⟨n, hn⟩
    by_contra h
    push_neg at h
    have eq3 : k ≥ 487 := by 
      omega 
    have eq4 : k * n + k * (k - 1) / 2 = 3^11 := by
      have eq1 : ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by 
        have h2 : ∀ (k : ℕ), ∑ i in Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by 
          intro k 
          induction k with 
          | zero => 
            simp 
          | succ k ih => 
            simp [Finset.sum_range_succ] at ih ⊢ 
            cases k with 
            | zero => 
              all_goals 
                omega 
            | succ k => 
              simp [add_assoc] at ih ⊢ 
              <;> ring_nf at ih ⊢ 
              <;> omega 
        specialize h2 k 
        linarith [h2]
      rw [eq1] at hn 
      linarith 
    have eq3 : k ≥ 487 := by 
      omega 
    have eq4' : k ≤ 771 := by 
      by_contra h6
      push_neg at h6 
      have eq5 : k * n + k * (k - 1) / 2 ≥ 3^11 + 1 := by
        have eq6 : k ≥ 772 := by 
          omega 
        have eq7 : k * (k - 1) / 2 ≥ 177148 := by 
          have h8 : k ≥ 772 := eq6 
          have h9 : k - 1 ≥ 771 := by 
            omega 
          have h10 : k * (k - 1) ≥ 772 * 771 := by 
            nlinarith [h8, h9]
          have h11 : k * (k - 1) / 2 ≥ 177148 := by 
            omega 
          linarith 
        omega 
      linarith [eq4, eq5] 
    interval_cases k <;> omega 
    all_goals omega