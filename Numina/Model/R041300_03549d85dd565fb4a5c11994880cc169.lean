import Mathlib

theorem algebra_605307 :
  IsLeast {t : ℝ | ∃ x y : ℝ, x ∈ Set.Icc 0 1 ∧ y ∈ Set.Icc 0 1 ∧ t = max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y)} (4 / 9) := by
  constructor
  · -- Show that 4/9 is in the set
    use 2 / 3, 2 / 3
    constructor
    · norm_num [Set.mem_Icc]
    constructor
    · norm_num [Set.mem_Icc]
    · norm_num [max_eq_left, max_eq_right]
  · -- Show that 4/9 is minimal
    intro t ht
    rcases ht with ⟨x, y, hx, hy, heq⟩
    rw [Set.mem_Icc] at hx hy
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    by_contra h
    push_neg at h
    have h1 : max (max (x * y) ((x - 1) * (y - 1))) (x + y - 2 * x * y) < 4 / 9 := by linarith
    by_cases h2 : x * y ≥ (x - 1) * (y - 1)
    · -- If x * y ≥ (x - 1) * (y - 1), then max (x * y) ((x - 1) * (y - 1)) = x * y
      have h3 : max (x * y) ((x - 1) * (y - 1)) = x * y := by
        apply max_eq_left
        linarith
      rw [h3] at h1
      by_cases h4 : x * y ≥ x + y - 2 * x * y
      · -- If x * y ≥ x + y - 2 * x * y, then max (x * y) (x + y - 2 * x * y) = x * y
        have h5 : max (x * y) (x + y - 2 * x * y) = x * y := by
          apply max_eq_left
          linarith
        rw [h5] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y)]
      · -- else: x * y < x + y - 2 * x * y, so max is the second
        have h6 : max (x * y) (x + y - 2 * x * y) = x + y - 2 * x * y := by
          apply max_eq_right
          linarith
        rw [h6] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y)]
    · -- else: (x - 1) * (y - 1) > x * y, so max is the second
      have h3 : max (x * y) ((x - 1) * (y - 1)) = (x - 1) * (y - 1) := by
        apply max_eq_right
        linarith
      rw [h3] at h1
      by_cases h4 : (x - 1) * (y - 1) ≥ x + y - 2 * x * y
      · -- If (x - 1) * (y - 1) ≥ x + y - 2 * x * y, then max is the first
        have h5 : max ((x - 1) * (y - 1)) (x + y - 2 * x * y) = (x - 1) * (y - 1) := by
          apply max_eq_left
          linarith
        rw [h5] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y)]
      · -- else: (x - 1) * (y - 1) < x + y - 2 * x * y, so max is the second
        have h6 : max ((x - 1) * (y - 1)) (x + y - 2 * x * y) = x + y - 2 * x * y := by
          apply max_eq_right
          linarith
        rw [h6] at h1
        nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3), sq_nonneg (x - y)]