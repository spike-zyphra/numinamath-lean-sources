import Mathlib

theorem number_theory_65305 :
    ∃ a : ℕ → ℕ,
      (∀ n, 0 < a n) ∧
      (∀ k ≥ 1, (∏ i in Finset.Icc 1 k, (a i - 1)) ∣ (∏ i in Finset.Icc 1 k, a i) + 1) := by
  use fun _ => 2
  constructor
  · -- Show that all terms are positive
    intro n
    all_goals norm_num
  · -- Show the divisibility property for each k ≥ 1
    intro k hk
    have h1 : ∀ k ≥ 1, (∏ i in Finset.Icc 1 k, (2 - 1 : ℕ)) = 1 := by
      intro k hk
      have h2 : ∀ k ≥ 1, (∏ i in Finset.Icc 1 k, (2 - 1 : ℕ)) = 1 := by
        intro k hk
        have h3 : (∏ i in Finset.Icc 1 k, (2 - 1 : ℕ)) = 1 := by
          simp
        exact h3
      exact h2 k hk
    have h2 : (∏ i in Finset.Icc 1 k, ( (2 : ℕ) - 1 : ℕ)) = 1 := h1 k hk
    have h3 : (∏ i in Finset.Icc 1 k, (2 : ℕ)) = 2 ^ k := by
      have h4 : ∀ k : ℕ, (∏ i in Finset.Icc 1 k, (2 : ℕ) ) = 2 ^ k := by
        intro k
        induction k with
        | zero =>
          simp
        | succ k ih =>
          rw [Finset.prod_Icc_succ_top (by norm_num)]
          rw [ih]
          ring
      exact h4 k
    have h4 : (∏ i in Finset.Icc 1 k, (2 : ℕ)) + 1 = 2 ^ k + 1 := by
      rw [h3]
      all_goals omega
    rw [h2]
    have h6 : 1 ∣ (∏ i in Finset.Icc 1 k, (2 : ℕ)) + 1 := by
      rw [h4]
      all_goals simp
    exact h6