import Mathlib

theorem algebra_517 {x y : ℚ} (h1 : 3 * x + y = 13 / 2) (h2 : 2 * x - ⌊y⌋ = 7 / 3) :
    x = 5 / 3 ∧ y = 3 / 2 := by
  have h3 : (⌊y⌋ : ℚ) ≤ y := by
    exact Int.floor_le y
  have h4 : y < (⌊y⌋ + 1 : ℚ) := by
    exact Int.lt_floor_add_one y
  let n := ⌊y⌋
  have hn1 : (n : ℚ) ≤ y := by
    exact_mod_cast h3
  have hn2 : y < (n + 1 : ℚ) := by
    exact_mod_cast h4
  have h2' : 2 * x - (n : ℚ) = 7 / 3 := by
    simpa using h2
  have h3x : x = 7 / 6 + (n : ℚ) / 2 := by
    have eq1 : 2 * x = 7 / 3 + (n : ℚ) := by
      linarith [h2']
    linarith
  have h4y : y = 3 - 3 / 2 * (n : ℚ) := by
    have eq2 : 3 * x + y = 13 / 2 := h1
    rw [h3x] at eq2
    linarith
  have h5 : (n : ℚ) ≤ 3 - 3 / 2 * (n : ℚ) := by
    linarith [hn1, h4y]
  have h6 : 3 - 3 / 2 * (n : ℚ) < (n + 1 : ℚ) := by
    linarith [hn2, h4y]
  have h7 : n ≤ 1 := by
    by_contra h
    push_neg at h
    have h8 : n ≥ 2 := by omega
    have h9 : (n : ℚ) ≥ (2 : ℚ) := by exact_mod_cast h8
    nlinarith
  have h8 : n > 0 := by
    by_contra h
    push_neg at h
    have h9 : n ≤ 0 := by omega
    have h10 : (n : ℚ) ≤ (0 : ℚ) := by exact_mod_cast h9
    nlinarith
  have h9 : n = 1 := by
    omega
  have hn3 : (n : ℚ) = 1 := by
    exact_mod_cast h9
  constructor
  · -- Solving for x
    rw [h3x]
    linarith [hn3]
  · -- Solving for y
    rw [h4y]
    linarith [hn3]