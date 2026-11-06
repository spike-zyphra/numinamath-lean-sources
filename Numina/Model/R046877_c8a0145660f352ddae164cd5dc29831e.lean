import Mathlib

theorem number_theory_3110 : IsGreatest {d | ∃ N : ℕ, (1 * 2 * 3 * ∏ i ∈ Finset.Icc 4 2020, i) = N * 37^d} 55 := by
  constructor
  · -- Show 55 is in the set
    use ( (1 * 2 * 3 * ∏ i ∈ Finset.Icc 4 2020, i) / (37 ^ 55) )
    native_decide
  · -- Show that 55 is greatest
    intro d
    intro h
    rcases h with ⟨N, hN⟩
    by_contra h'
    push_neg at h'
    have h2 : d ≥ 56 := by
      omega
    -- Now proving that $37^{56}\nmid 2020!$.
    have h3 : (37 ^ 56) ∣ (1 * 2 * 3 * ∏ i ∈ Finset.Icc 4 2020, i) := by
      have h4 : (37 ^ 56) ∣ (N * 37 ^ d) := by
        have h5 : (37 ^ 56) ∣ (37 ^ d) := by
          have h6 : 56 ≤ d := by
            omega
          have h7 : (37 ^ 56) ∣ (37 ^ d) := by
            exact pow_dvd_pow _ h6
          assumption
        -- Let's establish that N * 37^d is divisible by 37^56.
        have h8 : (37 ^ 56) ∣ (N * 37 ^ d) := by
          have h5' : (37 ^ 56) ∣ (37 ^ d) := h5
          -- Use divisibility property.
          have h9 : (37 ^ 56) ∣ (N * 37 ^ d) := by
            apply dvd_trans h5' 
            use N 
            all_goals ring 
            all_goals tauto
          assumption
        assumption
      -- Use the equality hypothesis.
      rw [show (1 * 2 * 3 * ∏ i ∈ Finset.Icc 4 2020, i) = N * 37^d by linarith [hN]] at *
      all_goals try { omega }
      all_goals try { assumption }
    have h4 : ¬ (37 ^ 56 ∣ (1 * 2 * 3 * ∏ i ∈ Finset.Icc 4 2020, i)) := by
      native_decide
    -- This yields a contradiction.
    exact h4 h3