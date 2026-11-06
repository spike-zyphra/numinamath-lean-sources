import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_295531 (f : ℝ → ℝ → ℂ)
  (h₀ : ∀ x y, f x y = (Real.cos (x^2) / Real.sin (y^2)) + (Real.cos (y^2) / Real.sin (x^2)) * .I)
  (h₁ : ∀ x y, x ∈ Set.Icc (-Real.sqrt (Real.pi / 2)) (Real.sqrt (Real.pi / 2)) →
    y ∈ Set.Icc (-Real.sqrt (Real.pi / 2)) (Real.sqrt (Real.pi / 2)) →
    abs (f x y) = Real.sqrt 2) :
  IsGreatest {x | ∃ a b, x = abs (f a b - (a + b * .I))} (Real.sqrt 2 - Real.sqrt (Real.pi / 2)) ∧
  IsLeast {x | ∃ a b, x = abs (f a b - (a + b * .I))} (Real.sqrt 2 - Real.sqrt (Real.pi / 2)) := by
  have h2 := h₁ (0 : ℝ) (0 : ℝ) (by
    constructor
    · -- Show that -√(π / 2) ≤ (0 : ℝ)
      have h1 : -Real.sqrt (Real.pi / 2) ≤ (0 : ℝ) := by
        have h2 : Real.sqrt (Real.pi / 2) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith [Real.pi_pos]
        linarith [show Real.sqrt (Real.pi / 2) ≥ 0 by positivity]
      linarith
    · -- Show that (0 : ℝ) ≤ Real.sqrt (Real.pi / 2)
      have h2 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
        apply Real.sqrt_nonneg
      linarith
  ) (by
    constructor
    · -- Show that -√(π / 2) ≤ (0 : ℝ)
      have h1 : -Real.sqrt (Real.pi / 2) ≤ (0 : ℝ) := by
        have h2 : Real.sqrt (Real.pi / 2) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith [Real.pi_pos]
        linarith [show Real.sqrt (Real.pi / 2) ≥ 0 by positivity]
      linarith
    · -- Show that (0 : ℝ) ≤ Real.sqrt (Real.pi / 2)
      have h2 : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := by
        apply Real.sqrt_nonneg
      linarith
  )
  -- Substitute `f 0 0` in `h2` using `h₀`.
  norm_num [h₀] at h2
  -- The above larger part cannot simplify expressions with division by zero.
  -- After simplification, `0 = Real.sqrt 2`, which is a contradiction as sqrt 2 > 0.
  -- Thus use `simp` on a contradiction.
  exfalso
  all_goals
    -- Use `linarith`.
    linarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg (Real.pi / 2), Real.pi_pos, Real.sqrt_pos.mpr (show (Real.pi / 2 : ℝ) > 0 by linarith [Real.pi_pos, Real.sqrt_nonneg (Real.pi / 2)])]