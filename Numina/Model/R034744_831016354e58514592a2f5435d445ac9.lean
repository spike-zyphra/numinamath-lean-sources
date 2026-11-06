import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_275583 (f : ℝ → ℝ) (hf : f = λ x => min (4 * x + 1) (min (x + 2) (-2 * x + 4))) :
    IsGreatest (range f) (8 / 3) := by
  constructor
  · -- Show that 8/3 is in the range
    use 2 / 3
    rw [hf]
    norm_num [min_eq_left, min_eq_right]
    all_goals norm_num [min_eq_left, min_eq_right]
  · -- Show that 8/3 is the greatest
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp only [Set.mem_range, Set.mem_setOf_eq] at hx
    by_cases h1 : 4 * x + 1 ≤ min (x + 2) (-2 * x + 4)
    · -- Case where f(x) = 4x+1
      have h2 : min (4 * x + 1) (min (x + 2) (-2 * x + 4)) = 4 * x + 1 := by
        apply min_eq_left
        linarith
      have eq : min (4 * x + 1) (min (x + 2) (-2 * x + 4)) = 4 * x + 1 := h2
      rw [eq] at hx
      nlinarith [show 4 * x + 1 ≤ 8 / 3 by
        have h11 : 4 * x + 1 ≤ min (x + 2) (-2 * x + 4) := h1
        have h4 : 4 * x + 1 ≤ x + 2 := by
          have h5 : 4 * x + 1 ≤ min (x + 2) (-2 * x + 4) := h11
          have h7 : min (x + 2) (-2 * x + 4) ≤ x + 2 := by
            cases min_cases (x + 2) (-2 * x + 4) with
            | inl h => linarith
            | inr h => linarith
          nlinarith
        have h8 : 4 * x + 1 ≤ -2 * x + 4 := by
          have h5 : 4 * x + 1 ≤ min (x + 2) (-2 * x + 4) := h11
          have h7 : min (x + 2) (-2 * x + 4) ≤ -2 * x + 4 := by
            cases min_cases (x + 2) (-2 * x + 4) with
            | inl h => linarith
            | inr h => linarith
          nlinarith
        linarith
      ]
    · -- Case where f(x) = min(x+2, -2x+4)
      have h2 : min (4 * x + 1) (min (x + 2) (-2 * x + 4)) = min (x + 2) (-2 * x + 4) := by
        apply min_eq_right
        linarith
      have eq : min (4 * x + 1) (min (x + 2) (-2 * x + 4)) = min (x + 2) (-2 * x + 4) := h2
      rw [eq] at hx
      by_cases h3 : (x + 2) ≤ (-2 * x + 4)
      · -- Case where min(x+2, -2x+4) = x+2
        have h4 : min (x + 2) (-2 * x + 4) = x + 2 := by
          apply min_eq_left
          linarith
        have eq2 : min (x + 2) (-2 * x + 4) = x + 2 := h4
        rw [eq2] at hx
        nlinarith
      · -- Case where min(x+2, -2x+4) = -2x+4
        have h4 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := by
          apply min_eq_right
          linarith
        have eq2 : min (x + 2) (-2 * x + 4) = -2 * x + 4 := h4
        rw [eq2] at hx
        nlinarith