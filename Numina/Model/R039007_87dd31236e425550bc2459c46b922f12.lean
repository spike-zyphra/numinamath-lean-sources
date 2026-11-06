import Mathlib

theorem inequalities_190146 (f : ℝ → ℝ) (hf : f = λ x => x^8 - 6 * x^7 + 9 * x^6 - x^2 + 6 * x - 9) :
    ∀ x, f x < 0 ↔ x ∈ Set.Ioo (-1) 1 := by
  intro x
  have hfx : f x = (x - 3) ^ 2 * (x ^ 6 - 1) := by
    rw [hf]
    ring
  simp only [hfx, Set.mem_Ioo]
  constructor
  · -- Assume f x <0. Then x ∈ (-1, 1).
    intro h
    have h1 : (x - 3) ^ 2 > 0 := by
      by_contra h1
      push_neg at h1
      have : (x - 3) ^ 2 = 0 := by
        linarith [sq_nonneg (x - 3)]
      have : x - 3 = 0 := by
        rw [sq_eq_zero_iff] at this
        linarith
      have : x = 3 := by linarith
      rw [this] at h
      nlinarith
    have h2 : x ^ 6 - 1 < 0 := by
      nlinarith
    have h3 : x ^ 2 < 1 := by
      nlinarith [sq_nonneg (x ^ 3), sq_nonneg (x ^ 2 - 1)]
    constructor
    · -- Show -1 < x
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
    · -- Show x < 1
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
  · -- Assume x ∈ (-1, 1). Then f x <0.
    rintro ⟨h1, h2⟩
    have h3 : x ^ 2 < 1 := by
      nlinarith
    have h4 : x ^ 6 - 1 < 0 := by
      have h5 : x ^ 2 < 1 := h3
      have h6 : x ^ 6 = (x ^ 2) ^ 3 := by ring
      rw [h6]
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 2), sq_nonneg (x ^ 4), sq_nonneg (x * (x ^ 4)), sq_nonneg x, sq_nonneg (x + 1)]
    have h5 : (x - 3) ^ 2 > 0 := by
      have h6 : (x - 3) ^ 2 > 0 := by
        nlinarith [sq_nonneg (x - 3)]
      linarith
    nlinarith