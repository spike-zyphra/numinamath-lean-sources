import Mathlib

theorem algebra_302499 (a : ℕ → ℝ) (ha1 : a 1 = 5)
    (han : ∀ n ≥ 2, a n = (2 * a (n - 1) - 1) / (a (n - 1) - 2)) :
    ∑ i ∈ Finset.range 100, a (i + 1) = 400 := by 
  have ha2 : a 2 = 3 := by
    rw [han 2 (by norm_num)]
    rw [ha1]
    norm_num
  have h5 : ∀ (n : ℕ), a (2 * n + 1) = 5 ∧ a (2 * n + 2) = 3 := by
    intro n 
    induction n with
    | zero =>
      constructor 
      · -- Show a 1 = 5
        exact ha1
      · -- Show a 2 = 3
        exact ha2 
    | succ n ih =>
      have ha3 : a (2 * n + 3) = 5 := by
        have h6 : a (2 * n + 2) = 3 := by 
          exact ih.right
        rw [han (2 * n + 3) (by omega)]
        simp [h6]
        <;> norm_num 
      have ha4 : a (2 * (n + 1) + 1) = 5 := by
        ring_nf at ha3 ⊢ 
        linarith 
      have ha5 : a (2 * (n + 1) + 2) = 3 := by
        have h7 : a (2 * n + 3) = 5 := by
          exact ha3
        rw [han (2 * (n + 1) + 2) (by omega)]
        have h8 : (2 * (n + 1) + 2 : ℕ) - 1 = 2 * n + 3 := by 
          omega 
        rw [h8]
        simp [h7]
        <;> norm_num
      constructor
      · exact ha4 
      · exact ha5 
  have h6 : ∑ i in Finset.range 100, a (i + 1) = 400 := by
    have h9 : ∀ (k : ℕ), a (2 * k + 1) = 5 ∧ a (2 * k + 2) = 3 := h5 
    have h11 : ∑ i in Finset.range 100, a (i + 1) = 400 := by
      have eq1 : ∑ i in Finset.range 100, a (i + 1) = ∑ k in Finset.range 50, (a (2 * k + 1) + a (2 * k + 2)) := by 
        simp [Finset.sum_range_succ]
        <;> ring
      rw [eq1] 
      have h12 : ∀ k : ℕ, k < 50 → (a (2 * k + 1) + a (2 * k + 2) = (8 : ℝ)) := by 
        intro k hk 
        have h100 : a (2 * k + 1) = 5 := by 
          have h90 := (h5 k).left
          simpa using h90 
        have h101 : a (2 * k + 2) = 3 := by 
          have h91 := (h5 k).right 
          simpa using h91 
        linarith 
      have h13 : ∑ k in Finset.range 50, (a (2 * k + 1) + a (2 * k + 2)) = ∑ k in Finset.range 50, (8 : ℝ) := by 
        apply Finset.sum_congr 
        · rfl 
        · intro k hk 
          have h20 : k < 50 := by 
            simp at hk ⊢ 
            all_goals try linarith 
          have eq8 : a (2 * k + 1) + a (2 * k + 2) = (8 : ℝ) := h12 k h20 
          linarith 
      rw [h13] 
      norm_num 
    exact h11 
  exact h6 
  all_goals linarith