import Mathlib

theorem algebra_289594 {x y : ℝ} (h1 : 2 * x + ⌊y⌋ = 2022) (h2 : 3 * y + ⌊2 * x⌋ = 2023) :
    (x, y) = (1011, 1 / 3) := by
  let n := ⌊y⌋
  have hn1 : (n : ℝ) ≤ y := by
    exact Int.floor_le y
  have hn2 : y < (n + 1 : ℝ) := by
    exact Int.lt_floor_add_one y
  have h1' : 2 * x + (n : ℝ) = 2022 := by
    simpa using h1
  have h3 : 2 * x = 2022 - (n : ℝ) := by 
    linarith
  have h2' : 3 * y + (⌊2 * x⌋ : ℝ) = 2023 := by
    simpa using h2
  have h7 : ⌊2 * x⌋ = ⌊2022 - (n : ℝ)⌋ := by 
    rw [show 2 * x = 2022 - (n : ℝ) by linarith]
  have hn3 : ⌊2 * x⌋ = 2022 - n := by 
    rw [h7]
    simp [Int.floor_int]
  have h8 : (⌊2 * x⌋ : ℝ) = (2022 - n : ℝ) := by 
    exact_mod_cast hn3
  rw [h8] at h2'
  have h9 : y = (1 + (n : ℝ)) / 3 := by
    have h10 : 3 * y = 1 + (n : ℝ) := by
      nlinarith
    linarith
  have hn4 : (n : ℝ) ≤ (y : ℝ) := by
    linarith [hn1]
  have hn5 : (y : ℝ) < (n + 1 : ℝ) := by
    linarith [hn2]
  rw [h9] at hn4 hn5
  have hn6 : n ≤ 0 := by
    by_contra h
    push_neg at h
    have hn7 : n ≥ 1 := by omega
    have hn8 : (n : ℝ) ≥ 1 := by exact_mod_cast hn7
    nlinarith
  have hn7 : n ≥ 0 := by
    by_contra h
    push_neg at h
    have hn8 : n ≤ -1 := by omega
    have hn9 : (n : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast hn8
    nlinarith
  have hn8 : n = 0 := by
    omega
  have h10 : 2 * x = 2022 := by
    have hn9 : (n : ℝ) = 0 := by exact_mod_cast hn8
    rw [hn9] at h3
    linarith
  have hx : x = 1011 := by
    linarith
  have hy : y = 1 / 3 := by
    rw [hn8] at h9
    nlinarith
  simp [hx, hy]