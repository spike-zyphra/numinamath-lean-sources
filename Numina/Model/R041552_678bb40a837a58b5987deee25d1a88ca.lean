import Mathlib

theorem number_theory_126013 : IsGreatest {k | ∃ m : ℤ, ∏ i ∈ Finset.Icc 20 2020, i = 26^k * m} 165 := by
  constructor
  · -- Show 165 is in the set
    use (∏ i ∈ Finset.Icc 20 2020, i) / 26 ^ 165
    native_decide
  · -- Show 165 is maximal
    intro k' hk 
    rcases hk with ⟨m, hm⟩
    by_contra h'
    push_neg at h'
    have h1 : k' ≥ 166 := by omega
    -- Show that if k' ≥ 166, then 26^166 divides the product
    have h2 : (26 : ℤ) ^ 166 ∣ ∏ i ∈ Finset.Icc 20 2020, i := by
      have h3 : (26 : ℤ) ^ k' ∣ ∏ i ∈ Finset.Icc 20 2020, i := by
        use m
        all_goals linarith [hm]
      have h4 : (26 : ℤ) ^ 166 ∣ (26 : ℤ) ^ k' := by 
        apply pow_dvd_pow
        all_goals omega
      have h5 : (26 : ℤ) ^ 166 ∣ ∏ i ∈ Finset.Icc 20 2020, i := by 
        exact dvd_trans h4 h3
      exact h5
    -- Show that 26^166 does not divide the product, resulting in a contradiction
    have h3 : ¬ ( (26 : ℤ) ^ 166 ∣ ∏ i ∈ Finset.Icc 20 2020, i ) := by
      native_decide
    exact h3 h2