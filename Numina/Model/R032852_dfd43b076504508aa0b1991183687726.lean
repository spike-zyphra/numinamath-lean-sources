import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_317456 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1)) :
  ∀ x ∈ Icc 0 8, f x ∈ Icc 0 4 := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hfx : f x = sqrt (x * (x ^ 2 + 8) * (8 - x)) / (x + 1) := h₀ x
  have h1 : 0 ≤ f x := by
    rw [hfx]
    apply div_nonneg
    · -- Show that sqrt (x * (x ^ 2 + 8) * (8 - x)) ≥ 0
      positivity
    · -- Show that (x + 1) ≥ 0
      linarith
  have h5a : f x ≤ 4 := by
    rw [hfx]
    have h4 : sqrt (x * (x ^ 2 + 8) * (8 - x)) ≤ 4 * (x + 1) := by
      have h5 : x * (x ^ 2 + 8) * (8 - x) ≤ 16 * (x + 1) ^ 2 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (x * (x - 2)), sq_nonneg ((x - 2) * (x + 1)), sq_nonneg ((x - 4) * (x - 2)), sq_nonneg (x - 4), sq_nonneg (x), sq_nonneg ((x + 1) - 3), sq_nonneg ((x - 2) ^ 2), sq_nonneg ((x - 2) * (x - 4)), sq_nonneg ((x - 2) * (x)), sq_nonneg ((x - 4) * (x)), mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ 8 - x by nlinarith)]
      have h7a : sqrt (x * (x ^ 2 + 8) * (8 - x)) ≤ Real.sqrt (16 * (x + 1) ^ 2) := by
        apply Real.sqrt_le_sqrt
        all_goals
        nlinarith [show x * (x ^ 2 + 8) * (8 - x) ≥ 0 by
          have hx2 : x ≥ 0 := hx0
          have hx3 : x ^ 2 + 8 ≥ 0 := by nlinarith
          have hx4 : 8 - x ≥ 0 := by linarith
          positivity
        ]
      have h8 : Real.sqrt (16 * (x + 1) ^ 2) = 4 * (x + 1) := by
        have h89 : 16 * (x + 1) ^ 2 = (4 * (x + 1)) ^ 2 := by
          ring_nf
        rw [h89]
        have h90 : 4 * (x + 1) ≥ 0 := by
          linarith
        rw [Real.sqrt_sq (h90)]
      linarith [h7a, h8]
    have h2 : 0 < x + 1 := by linarith
    apply (div_le_iff₀ (by linarith)).mpr
    linarith [h4]
  constructor
  · -- Show that 0 ≤ f x
    linarith [h1]
  · -- Show that f x ≤ 4
    linarith [h5a]