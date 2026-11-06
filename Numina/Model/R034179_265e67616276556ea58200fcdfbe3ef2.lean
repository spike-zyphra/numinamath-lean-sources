import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_314322 {f : ℝ → ℝ} (hf : f = λ x => x / (x ^ 2 + 1)) :
    IsGreatest (range f) (1 / 2) ∧ IsLeast (range f) (-1 / 2) := by
  constructor
  · -- Show 1/2 is the greatest element in the range
    constructor
    · -- Show 1/2 is achievable, by f(1) = 1/2
      use 1
      rw [hf]
      norm_num
    · -- Show no greater value is in the range
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h1 : x / (x ^ 2 + 1) ≤ 1 / 2 := by
        have h2 : x ^ 2 + 1 > 0 := by
          nlinarith [sq_nonneg x]
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [sq_nonneg (x - 1)]
      linarith
  · -- Show -1/2 is the least element in the range
    constructor
    · -- Show -1/2 is achievable, by f(-1) = -1/2
      use -1
      rw [hf]
      norm_num
    · -- Show no smaller value is in the range
      intro y
      rintro ⟨x, hx⟩
      rw [hf] at hx
      simp at hx
      have h1 : x / (x ^ 2 + 1) ≥ -1 / 2 := by
        have h2 : x ^ 2 + 1 > 0 := by
          nlinarith [sq_nonneg x]
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (x + 1)]
      linarith