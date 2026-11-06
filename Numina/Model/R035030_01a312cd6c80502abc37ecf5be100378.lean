import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_314343
  (a : ℕ → ℝ)
  (h₀ : a 0 = 1 / 3)
  (h₁ : ∀ n, a (n + 1) = Real.sqrt ((1 + a n) / 2)) :
  Monotone a := by 
  have h_nonneg : ∀ k : ℕ, 0 ≤ a k := by 
    intro k
    induction k with 
    | zero => 
      rw [h₀]
      norm_num 
    | succ k ih => 
      have h₂ : a (k + 1) = Real.sqrt ((1 + a k) / 2) := by
        specialize h₁ k 
        simpa using h₁ 
      rw [h₂]
      have h₃ : 0 ≤ a k := ih 
      have h₄ : (1 + a k) / 2 ≥ 0 := by 
        linarith 
      have h₅ : Real.sqrt ((1 + a k) / 2) ≥ 0 := by 
        apply Real.sqrt_nonneg 
      linarith
  have h_le1 : ∀ k : ℕ, a k ≤ 1 := by 
    intro k 
    induction k with 
    | zero => 
      rw [h₀]
      norm_num 
    | succ k ih => 
      have h₃ : a (k + 1) = Real.sqrt ((1 + a k) / 2) := by 
        specialize h₁ k 
        simpa using h₁ 
      rw [h₃] 
      have h₄ : a k ≤ 1 := ih 
      have h_nonneg1 : 0 ≤ a k := by 
        specialize h_nonneg k 
        linarith 
      have h₅ : (1 + a k) / 2 ≤ (1 : ℝ) := by 
        linarith 
      have h₆ : Real.sqrt ((1 + a k) / 2) ≤ (1 : ℝ) := by 
        have : Real.sqrt ((1 + a k) / 2) ≤ Real.sqrt ((1 : ℝ)) := Real.sqrt_le_sqrt (by linarith) 
        have h4 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one 
        linarith 
      linarith 
  have h2 : ∀ k : ℕ, a k ≤ a (k + 1) := by
    intro k 
    induction k with
    | zero => 
      have h3 : a 1 ≥ a 0 := by 
        have h₃ : a 1 = Real.sqrt ((1 + a 0) / 2) := by 
          specialize h₁ 0
          simpa using h₁ 
        rw [h₃, h₀]
        have h5 : Real.sqrt ((1 + (1 / 3 : ℝ)) / 2) ≥ (1 / 3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg ((1 + (1 / 3 : ℝ)) / 2), Real.sq_sqrt (show (0 : ℝ) ≤ (1 + (1 / 3 : ℝ)) / 2 by norm_num)]
        linarith 
      linarith 
    | succ k ih => 
      have h4 : a (k + 1) ≤ a (k + 2) := by 
        have h₃ : a (k + 2) = Real.sqrt ((1 + a (k + 1)) / 2) := by 
          specialize h₁ (k + 1)
          simpa using h₁ 
        rw [h₃]
        have h₆ : a (k + 1) ≥ 0 := by 
          specialize h_nonneg (k + 1)
          linarith 
        have h₅ : Real.sqrt ((1 + a (k + 1)) / 2) ≥ a (k + 1) := by
          have h8 : (1 + a (k + 1)) / 2 ≥ a (k + 1) ^ 2 := by 
            nlinarith [sq_nonneg (a (k + 1) - 1), sq_nonneg (a (k + 1) + 1 / 2), h_nonneg (k + 1), h_le1 (k + 1)]
          have h9 : Real.sqrt ((1 + a (k + 1)) / 2) ≥ a (k + 1) := by 
            have h_nonneg1 : 0 ≤ (1 + a (k + 1)) / 2 := by 
              have h7 : a (k + 1) ≥ 0 := by 
                specialize h_nonneg (k + 1)
                linarith 
              nlinarith 
            have h_nonneg2 : (Real.sqrt ((1 + a (k + 1)) / 2)) ^ 2 = (1 + a (k + 1)) / 2 := Real.sq_sqrt (by
              linarith 
            )
            nlinarith [Real.sqrt_nonneg ((1 + a (k + 1)) / 2), sq_nonneg (Real.sqrt ((1 + a (k + 1)) / 2) - a (k + 1)), sq_nonneg (a (k + 1) - 1)]
          linarith 
        linarith 
      linarith 
  intro n m hnm 
  have h3 : ∀ (k : ℕ), a n ≤ a (n + k) := by 
    intro k 
    induction k with 
    | zero => 
      simp 
    | succ k ih => 
      have h4 : a (n + k + 1) ≥ a (n + k) := by 
        specialize h2 (n + k) 
        simpa using h2 
      have h5 : a n ≤ a (n + k + 1) := by 
        have h6 : a n ≤ a (n + k) := ih 
        have h7 : a (n + k) ≤ a (n + k + 1) := by linarith [h4] 
        linarith 
      simpa using h5 
  have h5 : a n ≤ a m := by 
    have h6' : a n ≤ a (n + (m - n)) := h3 (m - n)
    have h6'' : a (n + (m - n)) = a m := by 
      have h7 : n + (m - n) = m := by 
        omega 
      rw [h7] 
    linarith [h6', h6''] 
  exact h5