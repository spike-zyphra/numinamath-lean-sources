import Mathlib


open Real


lemma lemma_1 {a : ℕ → ℝ} (ha : ∀ n, a n = (3 + √5)^n + (3 - √5)^n) :
    ∀ n, a (n + 2) = 6 * a (n + 1) - 4 * a n := by
  intro n
  have h1 : a (n + 2) = (3 + √5)^(n + 2) + (3 - √5)^(n + 2) := by
    rw [ha]
  have h2 : a (n + 1) = (3 + √5)^(n + 1) + (3 - √5)^(n + 1) := by
    rw [ha]
  have h3 : a n = (3 + √5) ^ n + (3 - √5) ^ n := by
    rw [ha]
  rw [h1, h2, h3]
  have eq1 : ((3 + √5 : ℝ) : ℝ) ^ (n + 2) = ((3 + √5) : ℝ) ^ n * ((3 + √5) ^ 2) := by
    ring_nf
  have eq2 : ((3 - √5) : ℝ) ^ (n + 2) = ((3 - √5) : ℝ) ^ n * ((3 - √5) ^ 2) := by
    ring_nf
  have eq3 : ((3 + √5) : ℝ) ^ (n + 1) = ((3 + √5) : ℝ) ^ n * (3 + √5) := by
    ring_nf
  have eq4 : ((3 - √5) : ℝ) ^ (n + 1) = ((3 - √5) : ℝ) ^ n * (3 - √5) := by
    ring_nf
  rw [eq1, eq2, eq3, eq4]
  have h4 : ((3 + √5) : ℝ) ^ 2 = 14 + 6 * √5 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h5 : ((3 - √5) : ℝ) ^ 2 = 14 - 6 * √5 := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  rw [h4, h5]
  ring_nf


theorem number_theory_26996 (n : ℕ) (hn : n > 0) :
    Odd ⌊(3 + √5)^n⌋ := by

  have h1 : ∃ k : ℤ, (3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n = (k : ℝ) := by
    have h2 : ∀ (n : ℕ), ∃ k : ℤ, (3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n = (k : ℝ) := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        use 2
        norm_num
      | succ n =>
        cases n with
        | zero =>
          use 6
          norm_num
          <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        | succ n =>
          have h3 := ih (n + 1) (by linarith)
          have h4 := ih (n) (by linarith)
          rcases h3 with ⟨k1, hk1⟩
          rcases h4 with ⟨k0, hk0⟩
          use 6 * k1 - 4 * k0
          have eq2 : (3 + √5 : ℝ) ^ (n + 2) + (3 - √5 : ℝ) ^ (n + 2) = 6 * ((3 + √5 : ℝ) ^ (n + 1) + (3 - √5 : ℝ) ^ (n + 1)) - 4 * ((3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n) := by
            have eq1 : ((3 + √5 : ℝ) : ℝ) ^ (n + 2) = ((3 + √5) : ℝ) ^ n * ((3 + √5) ^ 2) := by
              ring_nf
            have eq2 : ((3 - √5) : ℝ) ^ (n + 2) = ((3 - √5) : ℝ) ^ n * ((3 - √5) ^ 2) := by
              ring_nf
            have eq3 : ((3 + √5) : ℝ) ^ (n + 1) = ((3 + √5) : ℝ) ^ n * (3 + √5) := by
              ring_nf
            have eq4 : ((3 - √5) : ℝ) ^ (n + 1) = ((3 - √5) : ℝ) ^ n * (3 - √5) := by
              ring_nf
            rw [eq1, eq2, eq3, eq4]
            have h4 : ((3 + √5) : ℝ) ^ 2 = 14 + 6 * √5 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
            have h5 : ((3 - √5) : ℝ) ^ 2 = 14 - 6 * √5 := by
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
            rw [h4, h5]
            ring_nf
          rw [eq2]
          norm_num at hk1 hk0 ⊢
          all_goals
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    apply h2 n

  rcases h1 with ⟨k, hk⟩
  have hk_pos : (0 : ℝ) < (3 - √5 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have hk_lt_1 : (3 - √5 : ℝ) < (1 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h5 : (0 : ℝ) < (3 - √5 : ℝ) ^ n := by
    positivity
  have h6 : (3 - √5 : ℝ) ^ n < (1 : ℝ) := by
    have h5a : (3 - √5 : ℝ) < (1 : ℝ) := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    have h7 : (3 - √5 : ℝ) ^ n < (1 : ℝ) := by
      have h10 : (3 - √5 : ℝ) < (1 : ℝ) := h5a
      have h13 : (3 - √5 : ℝ) ^ n < (1 : ℝ) ^ n := by
        apply pow_lt_pow_left
        all_goals nlinarith
      have h16 : (1 : ℝ) ^ n = 1 := by
        simp
      linarith
    linarith
  -- Show that (3 + √5)^n + (3 - √5)^n = k
  have hk2 : (3 + √5 : ℝ) ^ n = (k : ℝ) - (3 - √5 : ℝ) ^ n := by
    have hk_eq : (3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n = (k : ℝ) := by
      linarith [hk]
    linarith
  -- Show that ⌊(3 + √5)^n⌋ = k - 1
  have h7 : ⌊(3 + √5 : ℝ) ^ n⌋ = k - 1 := by
    have hk_eq : (3 + √5 : ℝ) ^ n = (k : ℝ) - (3 - √5 : ℝ) ^ n := hk2
    have hk10 : (k - 1 : ℝ) < (3 + √5 : ℝ) ^ n := by
      have hk11 : (0 : ℝ) < (3 - √5 : ℝ) ^ n := h5
      have hk12 : (k - 1 : ℝ) < (k : ℝ) - (3 - √5 : ℝ) ^ n := by
        nlinarith
      rw [hk_eq]
      all_goals nlinarith
    have hk20 : (3 + √5 : ℝ) ^ n < (k : ℝ) := by
      have hk21 : (3 - √5 : ℝ) ^ n > 0 := by nlinarith
      have hk22 : (k : ℝ) - (3 - √5 : ℝ) ^ n < (k : ℝ) := by
        nlinarith
      rw [hk_eq]
      all_goals nlinarith
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> (try nlinarith)
  have hk8 : k % 2 = 0 := by
    have h8 : ∀ (n : ℕ), (∃ k : ℤ, (3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n = (k : ℝ) ∧ k % 2 = 0) := by
      intro n
      induction' n using Nat.strongRecOn with n ih
      cases n with
      | zero =>
        use 2
        constructor
        · norm_num
        · all_goals norm_num
      | succ n =>
        cases n with
        | zero =>
          use 6
          constructor
          · norm_num
          · all_goals norm_num
        | succ n =>
          have h3 := ih (n) (by linarith)
          rcases h3 with ⟨k0, hk0_eq, hk0_even⟩
          have h4 := ih (n + 1) (by linarith)
          rcases h4 with ⟨k1, hk1_eq, hk1_even⟩
          use 6 * k1 - 4 * k0
          constructor
          · -- Show that (3 + √5)^(n+2) + (3 - √5)^(n+2) = (6 * k1 - 4 * k0 : ℝ)
            have eq2 : (3 + √5 : ℝ) ^ (n + 2) + (3 - √5 : ℝ) ^ (n + 2) = 6 * ((3 + √5 : ℝ) ^ (n + 1) + (3 - √5 : ℝ) ^ (n + 1)) - 4 * ((3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n) := by
              have eq1 : ((3 + √5 : ℝ) : ℝ) ^ (n + 2) = ((3 + √5) : ℝ) ^ n * ((3 + √5) ^ 2) := by
                ring_nf
              have eq2 : ((3 - √5) : ℝ) ^ (n + 2) = ((3 - √5) : ℝ) ^ n * ((3 - √5) ^ 2) := by
                ring_nf
              have eq3 : ((3 + √5) : ℝ) ^ (n + 1) = ((3 + √5) : ℝ) ^ n * (3 + √5) := by
                ring_nf
              have eq4 : ((3 - √5) : ℝ) ^ (n + 1) = ((3 - √5) : ℝ) ^ n * (3 - √5) := by
                ring_nf
              rw [eq1, eq2, eq3, eq4]
              have h4 : ((3 + √5) : ℝ) ^ 2 = 14 + 6 * √5 := by
                nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
              have h5 : ((3 - √5) : ℝ) ^ 2 = 14 - 6 * √5 := by
                nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
              rw [h4, h5]
              ring_nf
            rw [eq2]
            norm_num at hk0_eq hk1_eq ⊢
            all_goals
              nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          · -- Show that k is even
            omega
    specialize h8 n
    rcases h8 with ⟨k0, hk0_eq, hk0_even⟩
    have hk9 : k = k0 := by
      have hk_eq0 : (3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n = (k : ℝ) := by
        linarith [hk]
      have hk0_eq0 : (3 + √5 : ℝ) ^ n + (3 - √5 : ℝ) ^ n = (k0 : ℝ) := by
        linarith [hk0_eq]
      have hk10 : (k : ℝ) = (k0 : ℝ) := by
        linarith
      exact_mod_cast hk10
    omega
  -- Show that k - 1 is odd
  rw [h7]
  have hk9 : (k - 1 : ℤ) % 2 = 1 := by
    omega
  have hk10 : Odd (k - 1 : ℤ) := by
    refine' Int.odd_iff.mpr (by omega)
  exact_mod_cast hk10