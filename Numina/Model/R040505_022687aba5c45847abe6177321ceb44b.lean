import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_131222 {a : ℝ} (A B : Set ℝ)
  (hA : A = {x | abs (x - (a + 1)^2 / 2) ≤ (a - 1)^2 / 2})
  (hB : B = {x | x^2 - 3 * (a + 1) * x + 2 * (3 * a + 1) ≤ 0}) :
  A ⊆ B ↔ 1 ≤ a ∧ a ≤ 3 ∨ a = -1 := by
  rw [hA, hB]
  constructor
  · -- First direction
    intro h
    have h1 : (2 * a) ^ 2 - 3 * (a + 1) * (2 * a) + 2 * (3 * a + 1) ≤ 0 := by
      apply h
      dsimp
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a ^ 2 - 2 * a), sq_nonneg (a - 1)]
    have h2 : (a^2 + 1) ^ 2 - 3 * (a + 1) * (a^2 + 1) + 2 * (3 * a + 1) ≤ 0 := by
      apply h
      dsimp
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (a ^ 2 - 2 * a), sq_nonneg (a - 1)]
    have h3 : a^2 ≥ 1 := by
      nlinarith
    by_cases h4 : 1 ≤ a
    · -- If 1 ≤ a
      have h5 : a ≤ 3 := by
        nlinarith [sq_nonneg (a ^ 2 - 3 * a), sq_nonneg (a - 1), sq_nonneg (a - 3), sq_nonneg (2 * a), sq_nonneg (a^2 - 3 * a - 1)]
      left
      constructor <;> linarith
    · -- If not 1 ≤ a
      have h5 : a < 1 := by linarith
      have h6 : a ≤ -1 := by nlinarith
      have h3 : (a + 1) * (a - 1) ≥ 0 := by nlinarith
      have h4 : a ^ 2 + 1 ≤ 2 := by nlinarith [sq_nonneg (a ^ 2 - 3 * a), sq_nonneg (a - 1), sq_nonneg (a - 3), sq_nonneg (2 * a), sq_nonneg (a^2 - 3 * a - 1)]
      have h5 : a ≥ -1 := by nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1)]
      have h6 : a = -1 := by nlinarith
      right
      linarith
  · -- Second direction
    rintro (h | h)
    · -- Case where 1 ≤ a ∧ a ≤ 3
      rcases h with ⟨h1, h2⟩
      intro x hx
      dsimp at hx ⊢
      rw [abs_le] at hx
      have h3 : 2 * a ≤ x := by nlinarith
      have h4 : x ≤ a^2 + 1 := by nlinarith
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - (3 * a + 1)), sq_nonneg (a - 1), sq_nonneg (a - 3)]
    · -- Case where a = -1
      intro x hx
      dsimp at hx ⊢
      rw [abs_le] at hx
      have h3 : -2 ≤ x := by nlinarith
      have h4 : x ≤ 2 := by nlinarith
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - (3 * a + 1)), sq_nonneg (a + 1)]