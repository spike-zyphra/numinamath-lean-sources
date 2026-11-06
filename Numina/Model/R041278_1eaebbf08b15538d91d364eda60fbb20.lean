import Mathlib

theorem number_theory_10107 : ∑ k in Finset.Icc (1:ℕ) 2008, ⌊((2008 * k / 2009 : ℝ) : ℝ)⌋ = 2015028 := by

  have h1 : ∀ k : ℕ, k ≥ 1 → k ≤ 2008 → ⌊((2008 * k / 2009 : ℝ) : ℝ)⌋ = (k - 1 : ℤ) := by
    intro k hk1 hk2
    have h3 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast show (k : ℝ) ≥ (1 : ℝ) by exact_mod_cast hk1
    have h4 : (k : ℝ) ≤ (2008 : ℝ) := by exact_mod_cast show (k : ℝ) ≤ (2008 : ℝ) by exact_mod_cast hk2

    have h5 : (2008 * (k : ℝ) / 2009 : ℝ) < (k : ℝ) := by
      have h8 : (2008 * (k : ℝ) ) < (k : ℝ) * 2009 := by
        nlinarith
      have h9 : (2008 * (k : ℝ) / 2009 : ℝ) < (k : ℝ) := by
        nlinarith
      linarith

    have h6 : (k - 1 : ℝ) < (2008 * (k : ℝ) / 2009 : ℝ) := by
      have h7 : (k : ℝ) ≥ (1 : ℝ) := by exact_mod_cast hk1
      have h8 : (k - 1 : ℝ) * 2009 < (2008 * (k : ℝ) ) := by
        nlinarith
      have h9 : (k - 1 : ℝ) < (2008 * (k : ℝ) / 2009 : ℝ) := by
        nlinarith
      linarith

    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith

  have h2 : ∑ k in Finset.Icc (1 : ℕ) 2008, ⌊((2008 * k / 2009 : ℝ) : ℝ)⌋ = ∑ k in Finset.Icc (1 : ℕ) 2008, (k - 1 : ℤ) := by
    apply Finset.sum_congr
    . rfl
    intro k hk
    have hk1 : k ≥ 1 := by
      have h2 : k ∈ Finset.Icc (1 : ℕ) 2008 := by
        exact hk
      simp at h2 ⊢
      all_goals linarith
    have hk2 : k ≤ 2008 := by
      have h1 : k ∈ Finset.Icc (1 : ℕ) 2008 := by
        exact hk
      simp at h1 ⊢
      all_goals linarith
    specialize h1 k hk1 hk2
    simpa using h1

  rw [h2]
  native_decide