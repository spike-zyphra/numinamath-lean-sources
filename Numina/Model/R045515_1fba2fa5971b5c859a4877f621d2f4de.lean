import Mathlib

theorem algebra_59629 : {x : ℝ | ⌊x⌋ * (x - ⌊x⌋) = 2005 * x} = {0, -1 / 2006} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First, prove that if x is a solution, then x ∈ {0, -1 / 2006}
    intro h
    have h1 : (⌊x⌋ : ℝ) ≤ x := by
      exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by
      exact Int.lt_floor_add_one x
    let n := ⌊x⌋
    have hn1 : (n : ℝ) ≤ x := h1
    have hn2 : x < (n + 1 : ℝ) := h2
    have hn3 : (n : ℝ) ≤ x := h1
    have hn4 : x < (n + 1 : ℝ) := h2
    have eq : (n : ℝ) * (x - (n : ℝ)) = 2005 * x := by
      simpa using h
    have h3 : n ≤ 0 := by
      by_contra h4
      push_neg at h4
      have h4 : n ≥ 1 := by omega
      have hn5 : (n : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show (n) ≥ (1) by omega)
      nlinarith
    have h4 : n ≥ -1 := by
      by_contra h4
      push_neg at h4
      have h4 : n ≤ -2 := by omega
      have hn5 : (n : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast (show (n) ≤ (-2) by omega)
      nlinarith
    have hn0 : n = -1 ∨ n = 0 := by omega
    rcases hn0 with (h11 | h11)
    · -- Assume n = -1
      have hn11 : (n : ℝ) = (-1 : ℝ) := by exact_mod_cast h11
      have h6 : x = (-1 / (2006 : ℝ)) := by
        nlinarith
      right
      linarith
    · -- Assume n = 0
      have hn11 : (n : ℝ) = (0 : ℝ) := by exact_mod_cast h11
      have h6 : x = (0 : ℝ) := by
        nlinarith
      left
      linarith
  · -- Show that {0, -1/2006} are solutions
    rintro (h0 | h1)
    · -- Assume x = 0
      rw [h0]
      norm_num
    · -- Assume x = -1 / 2006
      rw [h1]
      norm_num