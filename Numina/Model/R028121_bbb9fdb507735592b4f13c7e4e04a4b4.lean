import Mathlib

open Set Real

theorem algebra_11395 {a : ℝ} (A : Set ℝ) (hA : A = {x | -2 ≤ x ∧ x < 4}) (B : Set ℝ)
    (hB : B = {x | x ^ 2 - a * x - 4 ≤ 0}) (hBA : B ⊆ A) :
    0 ≤ a ∧ a < 3 := by

  have h1 : ∀ x, x ^ 2 - a * x - 4 ≤ 0 → -2 ≤ x ∧ x < 4 := by
    intro x hx
    have hx_in_B : x ∈ B := by
      rw [hB]
      exact hx
    have hx_in_A : x ∈ A := by 
      apply hBA 
      exact hx_in_B
    rw [hA] at hx_in_A
    exact hx_in_A

  have h2 := h1 ((a + Real.sqrt (a ^ 2 + 16)) / 2) (by 
    nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ a ^ 2 + 16 by nlinarith)]
  )

  have h3 := h1 ((a - Real.sqrt (a ^ 2 + 16)) / 2) (by
    nlinarith [Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ a ^ 2 + 16 by nlinarith)]
  )

  have h4 : -2 ≤ (a + Real.sqrt (a ^ 2 + 16)) / 2 := by
    linarith [h2.1]

  have h5 : (a + Real.sqrt (a ^ 2 + 16)) / 2 < (4 : ℝ) := by
    linarith [h2.2]

  have h6 : -2 ≤ (a - Real.sqrt (a ^ 2 + 16)) / 2 := by
    linarith [h3.1]

  have h7 : (a - Real.sqrt (a ^ 2 + 16)) / 2 < (4 : ℝ) := by
    linarith [h3.2]

  have h8 : 0 ≤ a := by
    nlinarith [sq_nonneg (Real.sqrt (a ^ 2 + 16) - (4 + a)), Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ a ^ 2 + 16 by nlinarith)]

  have h9 : a < 3 := by
    nlinarith [sq_nonneg (Real.sqrt (a ^ 2 + 16) - (8 - a)), Real.sqrt_nonneg (a ^ 2 + 16), Real.sq_sqrt (show 0 ≤ a ^ 2 + 16 by nlinarith)]

  constructor <;> linarith [h8, h9]