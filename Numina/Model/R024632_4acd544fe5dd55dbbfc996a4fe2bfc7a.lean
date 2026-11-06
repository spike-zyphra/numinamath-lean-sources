import Mathlib

theorem calculus_286395 (x : ℝ) (hx : ⌊x - 1 / 2⌋ = 3 * x - 5) : x = 2 := by
  let n := ⌊x - 1 / 2⌋
  have h1 : (n : ℝ) = 3 * x - 5 := by exact_mod_cast hx
  have h2 : (n : ℝ) ≤ x - 1 / 2 := by
    exact_mod_cast (Int.floor_le (x - 1 / 2))
  have h3 : x - 1 / 2 < (n + 1 : ℝ) := by
    exact_mod_cast (Int.lt_floor_add_one (x - 1 / 2))
  have h8 : n = 1 ∨ n = 2 := by
    have h11 : n ≤ 2 := by
      by_contra h
      push_neg at h
      have h14 : n ≥ 3 := by omega
      have h15 : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast h14
      nlinarith [h1, h2, h3, h14, h15]
    have h17 : n ≥ 1 := by
      by_contra h
      push_neg at h
      have h18 : n ≤ 0 := by omega
      have h19 : (n : ℝ) ≤ (0 : ℝ) := by exact_mod_cast h18
      nlinarith [h1, h2, h3, h18, h19]
    omega
  rcases h8 with (h8 | h8)
  · -- Assume n = 1
    have h9 : n = 1 := h8
    have h10 : (n : ℝ) = (1 : ℝ) := by
      exact_mod_cast h9
    have h11 : 3 * x - 5 = (1 : ℝ) := by
      nlinarith [h1, h10]
    have hx : x = (2 : ℝ) := by
      nlinarith [h11]
    exact hx
  · -- Assume n = 2
    have h9 : n = 2 := h8
    have h10 : (n : ℝ) = (2 : ℝ) := by
      exact_mod_cast h9
    exfalso
    nlinarith [h1, h10, h2, h3, h9]