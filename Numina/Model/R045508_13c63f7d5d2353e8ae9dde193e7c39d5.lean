import Mathlib

theorem algebra_11494: {x : ℝ | x ≠ -3 ∧ -x^2 = (3 * x + 1) / (x + 3)} = {-1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ≠ -3 ∧ -x^2 = (3 * x + 1) / (x + 3)
    intro h
    rcases h with ⟨hx1, heq⟩
    have hne : x + 3 ≠ 0 := by
      intro h'
      apply hx1
      linarith
    have eq1 : -x^2 * (x + 3) = (3 * x + 1) := by
      field_simp [hne] at heq ⊢
      nlinarith
    have eq2 : x ^ 3 + 3 * x ^ 2 + 3 * x + 1 = 0 := by
      nlinarith [eq1]
    have eq3 : (x + 1) ^ 3 = 0 := by
      ring_nf at eq2 ⊢
      nlinarith
    have eq4 : x + 1 = 0 := by
      have h1 : (x + 1) ^ 3 = 0 := eq3
      have h2 : x + 1 = 0 := by
        have h3 : (x + 1) ^ 3 = 0 := h1
        simp at h3 ⊢
        <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x ^ 2 + 2 * x + 1)]
      linarith
    -- From x + 1 = 0, we get x = -1
    linarith
  · -- Show that -1 is a solution
    intro heq
    rw [heq]
    constructor
    · norm_num
    · norm_num