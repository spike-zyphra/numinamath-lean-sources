import Mathlib

theorem algebra_199292 (x : ℝ) (hx : ⌊(x + 3) / 2⌋ ^ 2 - x = 1) : x = 0 := by 
  let n := ⌊(x + 3) / 2⌋
  have h1 : (n : ℝ) ^ 2 - x = 1 := by
    have h2 := hx
    simpa using h2

  have h2 : (n : ℝ) ≤ (x + 3) / 2 := by 
    exact Int.floor_le ((x + 3) / 2)

  have h3 : (x + 3) / 2 < (n + 1 : ℝ) := by 
    exact Int.lt_floor_add_one ((x + 3) / 2)

  have eq1 : x = (n : ℝ) ^ 2 - 1 := by linarith

  have h4 : (2 * (n : ℝ) - 3) ≤ x := by
    nlinarith

  have h5 : x < (2 * (n : ℝ) - 1) := by 
    nlinarith

  rw [eq1] at h4 h5

  have h6 : (n : ℝ) ^ 2 - 2 * (n : ℝ) + 2 ≥ 0 := by 
    nlinarith

  have h7 : (n : ℝ) * ( (n : ℝ) - 2 ) < 0 := by
    nlinarith

  have hn1 : n > 0 := by
    by_contra h
    push_neg at h
    have : (n : ℝ) ≤ (0 : ℝ) := by 
      exact_mod_cast h 
    nlinarith [show (n : ℝ) * ( (n : ℝ) - 2 ) ≥ 0 from by nlinarith]

  have hn2 : n < 2 := by 
    by_contra h 
    push_neg at h 
    have : (n : ℝ) ≥ (2 : ℝ) := by 
      exact_mod_cast h 
    nlinarith [show (n : ℝ) * ( (n : ℝ) - 2 ) ≥ 0 from by nlinarith]

  have hn3 : n = 1 := by
    omega

  have hn4 : (n : ℝ) = (1 : ℝ) := by
    exact_mod_cast hn3

  rw [hn4] at eq1
  linarith