import Mathlib

theorem inequalities_114400 (c : ℝ) (hc : c > 1)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < n → x n > 1)
    (hxs : ∀ n, 0 < n → ∑ i in Finset.Icc 1 n, x i < c) :
    ∃ a, 1 < a ∧ ∀ n, 0 < n → x n > a ^ n := by

  have h1 : ∀ (N : ℕ), (N ≥ 1) → ∑ i in (Finset.Icc 1 N), x i ≥ (N : ℝ) := by
    intro N hN
    have h4 : ∀ (i : ℕ), i ≥ 1 → x i > 1 := by
      intro i hi
      specialize hx i hi
      linarith
    have h5 : ∀ (k : ℕ), (k ≥ 1) → ∑ i in (Finset.Icc 1 k), x i ≥ (k : ℝ) := by
      intro k hk
      induction k with
      | zero => 
        linarith
      | succ k ih =>
        cases k with
        | zero =>
          norm_num at ih ⊢
          all_goals
            norm_num [Finset.sum_Icc_succ_top] at ih ⊢
            all_goals linarith [ih, h4 1 (by norm_num)]
        | succ k =>
          rw [Finset.sum_Icc_succ_top (by linarith)]
          simp at ih ⊢
          all_goals
            have h6 : x (k + 2) > 1 := by
              apply h4 (k + 2)
              omega
            norm_num at ih ⊢
            all_goals linarith [ih, h6]
    specialize h5 N hN
    simpa using h5

  have h2 : ∃ N : ℕ, (N ≥ 1) ∧ (∑ i in (Finset.Icc 1 N), x i ≥ (N : ℝ)) ∧ (∑ i in (Finset.Icc 1 N), x i < c) ∧ ((N : ℝ) ≥ (c + 1 : ℝ)) := by
    use Nat.ceil c + 1
    have h0 : (Nat.ceil c + 1 : ℕ) ≥ 1 := by
      have h4 : Nat.ceil c ≥ 1 := by
        have h5 : (c : ℝ) > 1 := by linarith
        have h6 : (c : ℝ) ≤ (Nat.ceil c : ℝ) := by
          exact Nat.le_ceil c
        by_contra h
        push_neg at h
        have h7 : Nat.ceil c = 0 := by
          omega
        have h8 : (c : ℝ) ≤ (0 : ℝ) := by
          have h9 : (Nat.ceil c : ℝ) = (0 : ℝ) := by
            exact_mod_cast h7
          nlinarith [show (c : ℝ) ≤ (Nat.ceil c : ℝ) from by exact_mod_cast Nat.le_ceil c, h9]
        nlinarith
      omega
    constructor
    · -- Show that `N ≥ 1`
      exact h0
    constructor
    · -- Show that `∑ i in Finset.Icc 1 (Nat.ceil c + 1), x i ≥ (Nat.ceil c + 1 : ℝ)`
      specialize h1 (Nat.ceil c + 1) h0
      norm_num at h1 ⊢
      exact_mod_cast h1
    constructor
    · -- Show that `∑ i in Finset.Icc 1 (Nat.ceil c + 1), x i < c`
      have h4 := hxs (Nat.ceil c + 1) (by omega)
      exact_mod_cast h4
    · -- Show that `(N : ℝ) ≥ (c + 1 : ℝ)`
      have h5' : ((Nat.ceil c + 1 : ℕ) : ℝ) ≥ (c + 1 : ℝ) := by
        have h7 : (↑(Nat.ceil c) : ℝ) ≥ (c : ℝ) := by exact_mod_cast Nat.le_ceil c
        have hN5 : ((Nat.ceil c + 1 : ℕ) : ℝ) = (↑(Nat.ceil c) : ℝ) + (1 : ℝ) := by
          norm_num
          <;> norm_cast
          <;> ring
        rw [hN5]
        linarith
      exact_mod_cast h5'

  rcases h2 with ⟨N, hN1, hN2, hN3, hN4⟩
  linarith