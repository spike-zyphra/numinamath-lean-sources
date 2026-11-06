import Mathlib

theorem algebra_267372 {x y : ℝ} (h1 : 2 * x + ⌊y⌋ = 2022) (h2 : 3 * y + ⌊2 * x⌋ = 2023) :
    x = 1011 ∧ y = 1 / 3 := by
  let n := ⌊y⌋
  have hn1 : (n : ℝ) ≤ y := by exact Int.floor_le y
  have hn2 : y < (n + 1 : ℝ) := by exact Int.lt_floor_add_one y
  have eq1 : 2 * x = 2022 - (n : ℝ) := by 
    have eq1 : 2 * x + (n : ℝ) = (2022 : ℝ) := by
      exact_mod_cast h1
    linarith
  have eq7 : ⌊(2 * x : ℝ)⌋ = 2022 - n := by
    have eq2 : (2 * x : ℝ) = (2022 - (n : ℝ) : ℝ) := by
      linarith [eq1]
    have : ⌊(2 * x : ℝ)⌋ = ⌊(2022 - (n : ℝ) : ℝ)⌋ := by
      rw [eq2]
    have eq5 : ⌊(2022 - (n : ℝ) : ℝ)⌋ = 2022 - n := by 
      have eq6 : (2022 - (n : ℝ) : ℝ) = (2022 - n : ℤ) := by
        norm_cast
      rw [eq6]
      simp
    rw [this, eq5]
  have eq8 : 3 * y + (2022 - (n : ℝ) : ℝ) = 2023 := by 
    have eq8 : (3 * y + ⌊2 * x⌋ : ℝ) = (2023 : ℝ) := by 
      exact_mod_cast h2 
    have eq9 : (⌊2 * x⌋ : ℝ) = (2022 - (n : ℝ) : ℝ) := by 
      have eq7' : ⌊(2 * x : ℝ)⌋ = 2022 - n := eq7 
      exact_mod_cast eq7' 
    rw [eq9] at eq8 
    linarith 
  have eq9 : 3 * y = 1 + (n : ℝ) := by 
    linarith [eq8] 
  have eq10 : y = (1 + (n : ℝ) ) / 3 := by 
    linarith [eq9]
  have h11 : (n : ℝ) ≤ (1 + (n : ℝ) ) / 3 := by 
    nlinarith [show (n : ℝ) ≤ y by exact_mod_cast hn1, eq10] 
  have h12 : n ≤ 0 := by 
    by_contra h
    push_neg at h
    have h13 : n ≥ 1 := by 
      omega 
    have h14 : (n : ℝ) ≥ (1 : ℝ) := by 
      exact_mod_cast show n ≥ 1 by omega 
    nlinarith [h11, h14] 
  have h13 : (1 + (n : ℝ) ) / 3 < (n + 1 : ℝ) := by 
    nlinarith [show y < (n + 1 : ℝ) by exact_mod_cast hn2, eq10] 
  have h14 : n ≥ 0 := by 
    by_contra h 
    push_neg at h 
    have h15 : n ≤ -1 := by 
      omega 
    have h16 : (n : ℝ) ≤ (-1 : ℝ) := by 
      exact_mod_cast show n ≤ -1 by omega 
    nlinarith [h13, h16] 
  have hn0 : n = 0 := by 
    linarith 
  have eq11 : x = (1011 : ℝ) := by 
    have eq12 : 2 * x = 2022 - (n : ℝ) := by 
      linarith [eq1] 
    have eq13 : (n : ℝ) = (0 : ℝ) := by 
      exact_mod_cast hn0 
    rw [eq13] at eq12 
    linarith 
  have eq12 : y = (1 / 3 : ℝ) := by 
    have eq13 : y = (1 + (n : ℝ) ) / 3 := by 
      linarith [eq10] 
    have eq14 : (n : ℝ) = (0 : ℝ) := by 
      exact_mod_cast hn0 
    rw [eq14] at eq13 
    linarith 
  constructor <;> linarith [eq11, eq12]