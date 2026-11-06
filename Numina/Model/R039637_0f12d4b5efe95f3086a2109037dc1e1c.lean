import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_245360 (f : ℝ → ℝ) (hf : ∀ x, 0 < x → f x = x - ⌊x⌋) :
    ∀ y, 0 ≤ y ∧ y < 1 ↔ ∃ x, 0 < x ∧ f x = y := by
  intro y
  constructor
  · -- Assume 0 ≤ y ∧ y < 1, we need to produce x > 0 such that f x = y
    rintro ⟨hy0, hy1⟩
    use y + 1
    constructor
    · -- Show that 0 < x
      linarith
    · -- Show that f x = y
      have h1 : f (y + 1) = (y + 1) - ⌊y + 1⌋ := by
        apply hf
        linarith
      rw [h1]
      have h2 : ⌊y + 1⌋ = 1 := by
        have h3 : 1 ≤ y + 1 := by
          linarith
        have h4 : y + 1 < (2 : ℝ) := by
          linarith
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> try nlinarith
      rw [h2]
      all_goals
        ring
  · -- Assume there exists x > 0 with f x = y, prove 0 ≤ y ∧ y < 1
    rintro ⟨x, hx_pos, hfx_eq_y⟩
    have hfx : f x = x - ⌊x⌋ := by
      apply hf x hx_pos
    rw [hfx] at hfx_eq_y
    constructor
    · -- Show that 0 ≤ y
      have h1 : (x - (⌊x⌋ : ℝ)) ≥ 0 := by
        have h2 : (⌊x⌋ : ℝ) ≤ x := by
          exact Int.floor_le x
        linarith
      linarith [hfx_eq_y, h1]
    · -- Show that y < 1
      have h2 : (x - (⌊x⌋ : ℝ)) < 1 := by
        have h3 : x < (⌊x⌋ + 1 : ℝ) := by
          exact Int.lt_floor_add_one x
        linarith
      linarith [hfx_eq_y, h2]