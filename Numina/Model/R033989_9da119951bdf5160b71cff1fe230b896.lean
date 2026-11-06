import Mathlib

theorem algebra_262632 :
  {x : ℝ | x ∈ Set.Icc 0 225 ∧ 375 + 8 * x = 425 + 8 * (225 - x)} = {115.625} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_Icc]
  constructor
  · -- Assume x is in the set
    rintro ⟨⟨hx1, hx2⟩, heq⟩
    have h1 : x ≥ 0 := by linarith
    have h2 : x ≤ 225 := by linarith
    have heq1 : x = (115.625 : ℝ) := by
      ring_nf at heq ⊢
      linarith
    rw [heq1]
    all_goals norm_num
  · -- Assume x is 115.625
    intro h
    rw [h]
    constructor
    · -- Show that 115.625 is in the interval [0, 225]
      constructor
      · -- Show it is >= 0
        norm_num
      · -- Show it is <= 225
        norm_num
    · -- Verify the equation at x = 115.625
      norm_num