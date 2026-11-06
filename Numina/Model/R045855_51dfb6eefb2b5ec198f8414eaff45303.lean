import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198282 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = abs (1 / x - ⌊1 / x + 1 / 2⌋)) :
  IsGreatest (range f) (1 / 2) := by
  constructor
  · -- Show that 1/2 belongs to the range of f
    use 2
    rw [h₀]
    norm_num [Int.floor_eq_iff]
    all_goals norm_num
  · -- Show that 1/2 is the greatest value in the range
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    have h1 : -1 / 2 ≤ (1 / x - ⌊1 / x + 1 / 2⌋ : ℝ) ∧ (1 / x - ⌊1 / x + 1 / 2⌋ : ℝ) ≤ 1 / 2 := by
      set n := ⌊1 / x + 1 / 2⌋ with hn
      have h2 : (n : ℝ) ≤ 1 / x + 1 / 2 := by
        have hn' : (n : ℝ) ≤ (1 / x + 1 / 2 : ℝ) := by
          exact Int.floor_le (1 / x + 1 / 2)
        linarith
      have h3 : (1 / x + 1 / 2 : ℝ) < (n + 1 : ℝ) := by
        have hn' : (1 / x + 1 / 2 : ℝ) < (n + 1 : ℝ) := by
          exact Int.lt_floor_add_one (1 / x + 1 / 2)
        linarith
      constructor
      · -- Show that -1/2 ≤ (1 / x - n)
        nlinarith
      · -- Show that (1 / x - n) ≤ 1/2
        nlinarith
    have h2 : abs (1 / x - ⌊1 / x + 1 / 2⌋ : ℝ) ≤ (1 / 2 : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith [h1.1, h1.2]
    linarith [h2, hx]