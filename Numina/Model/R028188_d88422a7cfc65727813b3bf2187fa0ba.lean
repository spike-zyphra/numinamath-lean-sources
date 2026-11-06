import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_318147 {f : ℝ → ℝ} (hf : f = λ x => x + 4 / x - 1)
  (x : ℕ → ℝ) (hx : ∀ i, x i ∈ Icc (1 / 4) 4)
  (h : ∑ i in Finset.range (n - 1), f (x i) = f (x n)) :
  n ≤ 6 := by 
  have h1 : ∀ i, f (x i) ≥ 3 := by
    intro i
    have hx10 : x i ∈ Icc (1 / 4) 4 := hx i
    rw [hf]
    rcases hx10 with ⟨hx11, hx12⟩
    have h5 : x i > 0 := by
      linarith
    have h6 : x i + 4 / x i - 1 ≥ 3 := by
      have h7 : x i + 4 / x i - 1 - 3 ≥ 0 := by
        have h8 : x i + 4 / x i - 1 - 3 = ( (x i) ^ 2 + 4 - x i - 3 * (x i) ) / (x i) := by 
          field_simp
          ring
        rw [h8]
        apply div_nonneg
        nlinarith [sq_nonneg (x i - 2)]
        all_goals nlinarith
      linarith
    linarith
  
  have h2 : ∀ i, x i ∈ Icc (1 / 4) 4 := by
    intro i
    exact hx i
  
  have h4 : ∀ i, f (x i) ≤ 15.25 := by
    intro i
    have hx10 : x i ∈ Icc (1 / 4) 4 := hx i
    rw [hf]
    rcases hx10 with ⟨hx11, hx12⟩
    have h5 : x i > 0 := by
      linarith
    have h6 : x i + 4 / x i - 1 ≤ 15.25 := by
      have h7 : x i + 4 / x i - 1 - 15.25 ≤ 0 := by
        have h8 : x i + 4 / x i - 1 - 15.25 = ( (x i) ^ 2 + 4 - x i - 15.25 * (x i) ) / (x i) := by 
          field_simp
          ring
        rw [h8]
        apply div_nonpos_of_nonpos_of_nonneg
        nlinarith [sq_nonneg (x i - 1 / 4), sq_nonneg (x i - 4)]
        all_goals nlinarith
      linarith
    linarith
  
  by_contra h'
  push_neg at h'
  have h7 : n ≥ 7 := by omega
  
  have h9 : ∀ i, f (x i) ≥ 3 := h1
  have h10 : ∀ i, x i ∈ Icc (1 / 4) 4 := h2
  have h11 : ∀ i, f (x i) ≤ 15.25 := h4
  have h14 : n - 1 ≥ 6 := by 
    omega
  
  -- Thus the sum from i = 0 to n - 2 has at least 6 terms
  -- So the sum is ≥ 6 * 3 = 18
  have h19 : ∑ i in Finset.range (n - 1), f (x i) ≥ 18 := by
    have h_n : n ≥ 7 := by 
      omega 
    have h8 : n - 1 ≥ 6 := by 
      omega 
    have h_nonneg : ∀ i : ℕ, i ∈ Finset.range (n - 1) → f (x i) ≥ (3 : ℝ) := by
      intros i hi
      have h10 : f (x i) ≥ 3 := by 
        apply h1
      exact h10
    have h20 : ∑ i in Finset.range (n - 1), f (x i) ≥ ∑ i in Finset.range (n - 1), (3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h21 : f (x i) ≥ (3 : ℝ) := h_nonneg i hi
      linarith
      all_goals try { tauto }
    have h21 : ∑ i in Finset.range (n - 1), (3 : ℝ) = (3 : ℝ) * (↑(n - 1) : ℝ) := by 
      simp [Finset.sum_const, Finset.card_range, mul_comm]
      <;> ring_nf <;> norm_num
      all_goals try { tauto } 
    have h22 : (3 : ℝ) * (↑(n - 1) : ℝ) ≥ (18 : ℝ) := by
      have h7 : (↑(n - 1) : ℝ) ≥ (6 : ℝ) := by 
        have h8 : (n - 1 : ℕ) ≥ (6 : ℕ) := by 
          omega 
        have h9 : (↑(n - 1 : ℕ) : ℝ) ≥ (↑(6 : ℕ) : ℝ) := by 
          exact_mod_cast h8 
        have h10 : (↑(6 : ℕ) : ℝ) = (6 : ℝ) := by norm_num
        have h11 : (↑(n - 1 : ℕ) : ℝ) = (↑(n - 1) : ℝ) := by 
          norm_num 
          all_goals try { norm_num }
          all_goals try { tauto }
        linarith [h9, h10] 
        all_goals try { norm_num }
        all_goals try { tauto } 
      nlinarith
      all_goals try { nlinarith }
      all_goals try { tauto }
    linarith [h20, h21, h22] 
    all_goals try { nlinarith }
    all_goals try { tauto }
  
  have h20 : ∑ i in Finset.range (n - 1), f (x i) = f (x n) := h
  have h23 : f (x n) ≤ 15.25 := by 
    have hx10 : x n ∈ Icc (1 / 4) 4 := h10 n 
    rw [hf]
    rcases hx10 with ⟨hx11, hx12⟩
    have h5 : x n > 0 := by 
      linarith 
    have h6 : x n + 4 / x n - 1 ≤ 15.25 := by 
      have h7 : x n + 4 / x n - 1 - 15.25 ≤ 0 := by 
        have h8 : x n + 4 / x n - 1 - 15.25 = ( (x n) ^ 2 + 4 - x n - 15.25 * (x n) ) / (x n) := by 
          field_simp 
          ring 
        rw [h8] 
        apply div_nonpos_of_nonpos_of_nonneg 
        nlinarith [sq_nonneg (x n - 1 / 4), sq_nonneg (x n - 4)]
        all_goals nlinarith 
        all_goals try { norm_num } 
        all_goals try { nlinarith } 
        all_goals try { tauto } 
      linarith 
    linarith 
  nlinarith [h19, h20, h23]