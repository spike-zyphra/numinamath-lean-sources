import Mathlib

theorem algebra_288626 {a : ℕ → ℝ} (ha1 : a 1 = 5)
    (han : ∀ n ≥ 2, a n = (2 * a (n - 1) - 1) / (a (n - 1) - 2)) :
    ∑ i ∈ Finset.range 100, a (i + 1) = 400 := by

  have ha2 : a 2 = 3 := by 
    specialize han 2 (by norm_num)
    rw [ha1] at han
    norm_num at han ⊢ 
    linarith

  have h5 : ∀ (n : ℕ), a (2 * n + 1) = 5 := by
    intro n 
    induction n with 
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have eq1 : 2 * (n + 1) + 1 = (2 * n + 2) + 1 := by ring 
      rw [eq1]
      have h6 : a (2 * n + 2) = 3 := by 
        have eq1 : (2 * n + 2 : ℕ) ≥ 2 := by omega 
        specialize han (2 * n + 2) eq1 
        have h10 : (2 * n + 2 - 1 : ℕ) = 2 * n + 1 := by omega 
        simp [h10, ih] at han 
        norm_num at han ⊢ 
        linarith 
      specialize han (2 * n + 2 + 1) (by linarith)
      have h10 : (2 * n + 2 + 1 - 1 : ℕ) = 2 * n + 2 := by omega 
      simp [h10, h6] at han 
      norm_num at han ⊢ 
      linarith

  have h6 : ∀ (n : ℕ), a (2 * n + 2) = 3 := by 
    intro n 
    have h9 : a (2 * n + 2) = 3 := by 
      have h5' : a (2 * n + 1) = 5 := by 
        apply h5 
      have eq1 : (2 * n + 2 : ℕ) ≥ 2 := by omega 
      specialize han (2 * n + 2) eq1 
      have h10 : (2 * n + 2 - 1 : ℕ) = 2 * n + 1 := by omega 
      simp [h10, h5'] at han 
      norm_num at han ⊢ 
      linarith 
    simpa using h9

  have h7 : ∀ (n : ℕ), ∑ i ∈ Finset.range (2 * n + 2), a (i + 1) = 8 * (↑n + 1) := by 
    intro n 
    induction n with 
    | zero =>
      norm_num [Finset.sum_range_succ, ha1, ha2]
    | succ n ih =>
      have eq1 : a (2 * n + 3) = 5 := by 
        specialize h5 (n + 1)
        simpa using h5 
      have eq2 : a (2 * n + 4) = 3 := by 
        specialize h6 (n + 1)
        simpa using h6 
      rw [show 2 * (n + 1) + 2 = (2 * n + 2) + 2 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [ih, eq1, eq2] at *
      <;> ring_nf <;> norm_num 
      all_goals linarith

  have h8 : ∑ i ∈ Finset.range 100, a (i + 1) = 400 := by 
    specialize h7 49 
    norm_num at h7 ⊢ 
    linarith

  exact h8