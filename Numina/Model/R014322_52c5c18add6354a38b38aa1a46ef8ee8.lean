import Mathlib

open Real

theorem algebra_8263 {x y : ℝ} (hx : ⌊x⌋ = ⌊y⌋) : |x - y| < 1 := by
  have h1 : ⌊x⌋ = ⌊y⌋ := hx
  have h2 : (⌊x⌋ : ℝ) ≤ x := by
    exact Int.floor_le x
  have h3 : x < (⌊x⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one x
  have h4 : (⌊y⌋ : ℝ) ≤ y := by
    exact Int.floor_le y
  have h5 : y < (⌊y⌋ + 1 : ℝ) := by
    exact Int.lt_floor_add_one y
  have h6 : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ) := by
    exact_mod_cast h1
  have h7 : (⌊x⌋ : ℝ) ≤ y := by
    linarith [h6, h4]
  have h8 : y < (⌊x⌋ + 1 : ℝ) := by
    linarith [h6, h5]
  have h9 : x - y < 1 := by
    linarith [h3, h7]
  have h10 : - (1 : ℝ) < x - y := by
    linarith [h2, h8]
  rw [abs_lt]
  constructor <;> linarith [h9, h10]