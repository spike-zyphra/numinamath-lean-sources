import Mathlib

open Finset Real

theorem inequalities_217847 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (hx : StrictAnti x) :
    x 0 - x n + ∑ i ∈ range n, (1 / (x i - x (i + 1))) ≥ 2 * n := by

  have h1 : ∀ i j, i < j → x i > x j := by
    intro i j h
    exact hx h

  have h2 : ∀ (i : ℕ), i < n → x i - x (i + 1) > 0 := by
    intro i hi
    have h : x i > x (i + 1) := by
      apply hx
      linarith
    linarith

  have h3 : x 0 - x n = ∑ i in range n, (x i - x (i + 1)) := by 
    have h4 : ∀ k : ℕ, ∑ i in range k, (x i - x (i + 1)) = x 0 - x k := by
      intro k
      induction k with
      | zero =>
        simp
      | succ k ih =>
        rw [sum_range_succ, ih]
        all_goals linarith
    specialize h4 n
    linarith

  rw [h3]

  have h4 : ∀ i ∈ range n, (x i - x (i + 1) : ℝ) > 0 := by
    intro i hi
    have h5 : i < n := by
      simp at hi ⊢
      all_goals linarith
    specialize h2 i h5
    linarith

  have h5 : ∑ i in range n, (x i - x (i + 1) : ℝ) + ∑ i in range n, (1 / (x i - x (i + 1)) : ℝ) ≥ 2 * n := by
    have h6 : ∀ i ∈ range n, (x i - x (i + 1) : ℝ) + 1 / (x i - x (i + 1)) ≥ (2 : ℝ) := by 
      intro i hi
      have h7 : (x i - x (i + 1) : ℝ) > 0 := by
        have h5 : i < n := by
          simp at hi ⊢
          all_goals linarith
        specialize h2 i h5
        linarith
      have h9 : (x i - x (i + 1) : ℝ) + 1 / (x i - x (i + 1) : ℝ) - (2 : ℝ) ≥ 0 := by
        have h12 : (x i - x (i + 1) : ℝ) + 1 / (x i - x (i + 1) : ℝ) - (2 : ℝ) = ((x i - x (i + 1) : ℝ) ^ 2 + 1 - 2 * (x i - x (i + 1) : ℝ) ) / (x i - x (i + 1) ) := by
          field_simp
          <;> ring
        rw [h12]
        have h13 : ((x i - x (i + 1) : ℝ) ^ 2 + 1 - 2 * (x i - x (i + 1) : ℝ) ) ≥ 0 := by
          have h14 : ((x i - x (i + 1) : ℝ) - 1 ) ^ 2 ≥ 0 := by
            exact sq_nonneg ((x i - x (i + 1) ) - 1 )
          linarith
        have h15 : (x i - x (i + 1) : ℝ) > 0 := h7
        apply div_nonneg
        exact h13
        all_goals
          linarith
      linarith
    have h10 : ∑ i in range n, (x i - x (i + 1) : ℝ) + ∑ i in range n, (1 / (x i - x (i + 1)) : ℝ) = ∑ i in range n, ((x i - x (i + 1) + 1 / (x i - x (i + 1)) ) : ℝ) := by 
      simp [sum_add_distrib]
    rw [h10]
    have h11 : ∑ i in range n, (x i - x (i + 1) + 1 / (x i - x (i + 1)) ) ≥ 2 * n := by 
      have h7 : ∀ i ∈ range n, (x i - x (i + 1) + 1 / (x i - x (i + 1)) ) ≥ (2 : ℝ) := h6 
      have h17 : ∑ i in range n, (x i - x (i + 1) + 1 / (x i - x (i + 1)) ) ≥ ∑ i in range n, (2 : ℝ) := by 
        apply sum_le_sum 
        all_goals 
          intro i hi 
          apply h7 i hi 
      have h18 : ∑ i in range n, (2 : ℝ) = 2 * n := by 
        simp [Finset.sum_const, Finset.card_range, mul_comm] 
        <;> nlinarith 
      linarith 
    linarith 
  linarith [h5]