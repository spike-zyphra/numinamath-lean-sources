import Mathlib

theorem algebra_301524 {x : ℝ} (hx : 6 * x - 3 * ⌊x⌋ + 7 = 0) :
    x = -19 / 6 ∨ x = -8 / 3 := by
  let n := ⌊x⌋
  have hn1 : n ≤ (x : ℝ) := by exact Int.floor_le x
  have hn2 : (x : ℝ) < (n + 1 : ℝ) := by exact Int.lt_floor_add_one x
  have h_eq : 6 * x - 3 * (n : ℝ) + 7 = 0 := by exact_mod_cast hx
  have h1 : (x : ℝ) = (3 * (n : ℝ) - 7) / 6 := by
    linarith
  have hn3 : n ≤ -3 := by
    by_contra h
    push_neg at h
    have h6 : n ≥ -2 := by 
      omega 
    have hn5 : (n : ℝ) ≥ (-2 : ℝ) := by exact_mod_cast h6 
    have h5 : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hn1 
    nlinarith [h1, h5, hn5, hx]
  have hn4 : n ≥ -4 := by
    by_contra h 
    push_neg at h 
    have h15 : n ≤ -5 := by 
      omega 
    have hn15 : (n : ℝ) ≤ (-5 : ℝ) := by exact_mod_cast h15 
    have hn25 : (x : ℝ) < ((n + 1) : ℝ) := by exact_mod_cast hn2 
    nlinarith [h1, hn25, hn15, hx]
  have hn5 : n = -4 ∨ n = -3 := by
    omega 
  rcases hn5 with (h | h)
  · -- case n = -4, means x = (3 * (-4) -7)/6 = (-12 -7)/6 = -19/6 
    have h6 : (n : ℝ) = (-4 : ℝ) := by exact_mod_cast h 
    have hx1 : x = (-19 / 6 : ℝ) := by 
      nlinarith [h6, h1]
    left 
    exact_mod_cast hx1 
  · -- case n = -3, means x = (3 * (-3) -7)/6 = (-9 -7)/6 = -16/6 = -8/3 
    have h6 : (n : ℝ) = (-3 : ℝ) := by exact_mod_cast h 
    have hx2 : x = (-8 / 3 : ℝ) := by 
      nlinarith [h6, h1]
    right 
    exact_mod_cast hx2