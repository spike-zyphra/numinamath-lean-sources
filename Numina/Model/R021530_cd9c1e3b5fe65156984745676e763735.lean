import Mathlib

lemma lemma_1 : Nat.factorization (Nat.factorial 2022) 13 = 166 := by
  native_decide

theorem number_theory_3002 : IsGreatest {d : ℕ | ∃ N : ℤ, ∏ i ∈ Finset.range 2022, (i + 1) = N * 26 ^ d} 166 := by 
  constructor
  · -- Show that 166 is in the set.
    use ( (∏ i in Finset.range 2022, (i + 1)) ) / (26 ^ 166)
    native_decide
  · -- Show that 166 is the greatest element in the set.
    intro d hd
    rcases hd with ⟨N, hN⟩
    have h1 : ( ∏ i ∈ Finset.range 2022, (i + 1) ) = (Nat.factorial 2022 : ℤ) := by 
      native_decide
    rw [h1] at hN

    by_contra h
    push_neg at h
    have h2 : d ≥ 167 := by omega

    have h4 : (26 : ℤ) ^ 167 ∣ (Nat.factorial 2022 : ℤ) := by 
      have h5 : (26 : ℤ) ^ d ∣ (Nat.factorial 2022 : ℤ) := by
        use N
        all_goals
        nlinarith
      have h6 : (26 : ℤ) ^ 167 ∣ (26 : ℤ) ^ d := by 
        exact pow_dvd_pow _ (by omega)
      exact dvd_trans h6 h5

    have h8 : ¬ (26 : ℤ) ^ 167 ∣ (Nat.factorial 2022 : ℤ) := by
      native_decide
    exact h8 h4