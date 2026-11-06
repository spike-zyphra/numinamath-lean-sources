import Mathlib


theorem algebra_285979 :
    IsLeast {x : ℤ | ∃ n : ℕ, n > 0 ∧ x = ∑ k in Finset.Icc 1 100, |(n : ℤ) - k|} 2500 := by
  constructor
  · -- Show 2500 is in the set
    use 50
    constructor
    · norm_num -- shows 50 > 0
    · native_decide -- computes the sum
  · -- Show 2500 is the minimum
    intro x hx
    rcases hx with ⟨n, hn_pos, hx_eq⟩
    have h1 : x = ∑ k in Finset.Icc 1 100, |(n : ℤ) - k| := by
      exact_mod_cast hx_eq
    have h2 : ∑ k in Finset.Icc 1 100, |(n : ℤ) - k| ≥ 2500 := by
      have h3 : n > 0 := by exact_mod_cast hn_pos
      by_cases h8 : n ≤ 100
      · -- If n ≤ 100, then we compute the sum from 1 to 100
        have h9 : n ≤ 100 := by omega
        have h10 : ∑ k in Finset.Icc 1 100, |(n : ℤ) - k| ≥ 2500 := by
          have h11 : n ≤ 100 := by omega
          interval_cases n <;> try { native_decide }
        linarith
      · -- n > 100
        have h12 : n > 100 := by omega
        have h13 : ∑ k in Finset.Icc 1 100, |(n : ℤ) - k| = 100 * (n : ℤ) - 5050 := by
          have h14 : ∀ k : ℤ, k ∈ Finset.Icc 1 100 → (n : ℤ) ≥ k := by
            intro k hk
            have h8 : k ≥ 1 := by
              have h9 : k ∈ Finset.Icc (1 : ℤ) 100 := by
                exact_mod_cast hk
              simp at h9 ⊢
              all_goals omega
            have h10 : k ≤ 100 := by
              have h9 : k ∈ Finset.Icc (1 : ℤ) 100 := by
                exact_mod_cast hk
              simp at h9 ⊢
              all_goals omega
            have h17 : (n : ℤ) ≥ 101 := by
              omega
            omega
          have h20 : ∑ k in Finset.Icc 1 100, |(n : ℤ) - k| = ∑ k in Finset.Icc 1 100, ((n : ℤ) - k) := by
            apply Finset.sum_congr
            · rfl
            · intro k hk
              have h19 : |((n : ℤ) - k)| = (n : ℤ) - k := by
                have h17 : (n : ℤ) ≥ k := by
                  apply h14 k
                  exact_mod_cast hk
                rw [abs_of_nonneg]
                omega
              rw [h19]
          rw [h20]
          have h23 : ∑ k in Finset.Icc 1 100, ((n : ℤ) - k) = 100 * (n : ℤ) - 5050 := by
            have h24 : ∑ k in Finset.Icc 1 100, ((n : ℤ) - k) = 100 * (n : ℤ) - (∑ k in Finset.Icc 1 100, (k : ℤ)) := by
              rw [Finset.sum_sub_distrib]
              simp [Finset.sum_const, Finset.card_range]
              all_goals ring
            rw [h24]
            have h25 : ∑ k in Finset.Icc 1 100, (k : ℤ) = 5050 := by
              native_decide
            linarith
          linarith
        have h16 : (n : ℤ) ≥ 101 := by
          omega
        omega
    have h3 : x ≥ 2500 := by
      linarith [h1, h2]
    linarith