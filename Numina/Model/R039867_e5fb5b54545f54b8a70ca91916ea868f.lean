import Mathlib

theorem algebra_276989 : ⌊Real.sqrt 5⌋ * (⌊Real.sqrt 5⌋ - 1 / (Real.sqrt 5 - ⌊Real.sqrt 5⌋))^3 = -10 * Real.sqrt 5 := by
  have h1 : ⌊Real.sqrt 5⌋ = 2 := by
    have h2 : 2 < Real.sqrt 5 := by
      rw [Real.lt_sqrt] <;> norm_num
    have h3 : Real.sqrt 5 < 3 := by
      rw [Real.sqrt_lt] <;> norm_num
    rw [Int.floor_eq_iff]
    constructor <;> (try norm_num) <;> try linarith

  have h2 : (Real.sqrt 5 - ⌊Real.sqrt 5⌋ : ℝ) = Real.sqrt 5 - 2 := by
    rw [h1]
    all_goals norm_num

  have h3 : 1 / (Real.sqrt 5 - ⌊Real.sqrt 5⌋ : ℝ) = Real.sqrt 5 + 2 := by
    rw [h2]
    have h4 : Real.sqrt 5 - 2 ≠ 0 := by
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (5 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    field_simp [h4]
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

  have h4 : (⌊Real.sqrt 5⌋ : ℝ) - 1 / (Real.sqrt 5 - ⌊Real.sqrt 5⌋ : ℝ) = -Real.sqrt 5 := by
    rw [h3]
    have h5 : (⌊Real.sqrt 5⌋ : ℝ) = 2 := by
      exact_mod_cast h1
    rw [h5]
    nlinarith

  rw [h4]
  have h5 : ⌊Real.sqrt 5⌋ = 2 := h1
  have h6 : (⌊Real.sqrt 5⌋ : ℝ) = 2 := by exact_mod_cast h5
  rw [h6]
  have h7 : (-Real.sqrt 5 : ℝ) ^ 3 = -5 * Real.sqrt 5 := by
    calc
      (-Real.sqrt 5 : ℝ) ^ 3 = - ((Real.sqrt 5 : ℝ) ^ 3) := by ring
      _ = - ((Real.sqrt 5 : ℝ) * (Real.sqrt 5 ^ 2)) := by ring
      _ = - ((Real.sqrt 5 : ℝ) * 5) := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      _ = - (5 * Real.sqrt 5) := by ring
      _ = -5 * Real.sqrt 5 := by ring

  rw [h7]
  all_goals
    ring