import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_105216 (f : ℝ → ℝ) (hf : f = λ x => (x^2 + x - 1)/(x^2 + x + 1)) :
    range f = {y | -5/3 ≤ y ∧ y < 1} := by
  ext y
  simp [hf, mem_range]
  constructor
  · -- Assume y in range of f
    rintro ⟨x, hx⟩
    have h2 : (x ^ 2 + x + 1) > 0 := by
      nlinarith [sq_nonneg (x + 1 / 2)]
    have h3 : y = (x ^ 2 + x - 1) / (x ^ 2 + x + 1) := by
      linarith [hx]
    have h4 : y * (x ^ 2 + x + 1) = x ^ 2 + x - 1 := by
      rw [h3]
      field_simp [show (x ^ 2 + x + 1) > 0 by nlinarith]
    have h5 : (y - 1) * (x ^ 2) + (y - 1) * x + (y + 1) = 0 := by
      nlinarith [h4]
    have h5' : (y - 1) ^ 2 - 4 * (y - 1) * (y + 1) ≥ 0 := by
      nlinarith [sq_nonneg ((y - 1) * x + (y - 1) / 2), sq_nonneg ((y - 1) ), sq_nonneg (x + (y - 1) / 2), sq_nonneg (x - (- (y - 1) / 2)), sq_nonneg ((y - 1) * (x + 1 / 2)), sq_nonneg (y - 1), sq_nonneg (x + 1 / 2)]
    constructor
    · -- Show that -5/3 ≤ y
      nlinarith
    · -- Show that y < 1
      by_contra h
      push_neg at h
      have h4 : y ≥ 1 := by linarith
      nlinarith [sq_nonneg ((x + 1 / 2) ), sq_nonneg ((y - 1) * x), h4, sq_nonneg (x - (-1/2)), sq_nonneg (y - 1/2), sq_nonneg ((y - 1) * (x + 1/2))]
  · -- Assume y in the interval
    rintro ⟨hy1, hy2⟩
    have h1 : y < 1 := hy2
    have h3 : (y - 1) ^ 2 - 4 * (y - 1) * (y + 1) ≥ 0 := by
      nlinarith
    have h4 : ∃ x : ℝ, y * (x ^ 2 + x + 1) = x ^ 2 + x - 1 := by
      by_cases h7 : y - 1 = 0
      · -- y - 1 = 0, so y = 1
        have h8 : y = 1 := by linarith
        nlinarith
      · -- y - 1 ≠ 0
        have h7 : (y - 1) ≠ 0 := by
          intro h0
          have : y = 1 := by linarith
          linarith
        have h8 : ∃ x : ℝ, (y - 1) * x ^ 2 + (y - 1) * x + (y + 1) = 0 := by
          have h2 : (y - 1) ≠ 0 := h7
          use (- (y - 1) + Real.sqrt ((y - 1) ^ 2 - 4 * (y - 1) * (y + 1))) / (2 * (y - 1))
          field_simp [h2]
          ring_nf
          rw [Real.sq_sqrt (by nlinarith)]
          <;> nlinarith
        rcases h8 with ⟨x, h3⟩
        use x
        nlinarith
    rcases h4 with ⟨x, h4⟩
    refine ⟨x, by
      have h2 : (x ^ 2 + x + 1) > 0 := by
        nlinarith [sq_nonneg (x + 1 / 2)]
      field_simp [show (x ^ 2 + x + 1) > 0 by nlinarith [sq_nonneg (x + 1/2)] ] at *
      nlinarith
    ⟩