import Mathlib

theorem algebra_13621 (f : ℝ → ℝ) (hf : f = fun x => (x + 1) / (x ^ 2 + 6 * x + 8)) :
    {x | x ^ 2 + 6 * x + 8 ≠ 0} = {x | x ≠ -4 ∧ x ≠ -2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- Assume x^2 + 6 * x + 8 ≠ 0, prove x ≠ -4 ∧ x ≠ -2
    intro h
    have h1 : x ≠ -4 := by
      by_contra h1
      have h2 : x ^ 2 + 6 * x + 8 = 0 := by
        rw [h1]
        norm_num
      contradiction
    have h2 : x ≠ -2 := by
      by_contra h2
      have h3 : x ^ 2 + 6 * x + 8 = 0 := by
        rw [h2]
        norm_num
      contradiction
    exact ⟨h1, h2⟩
  · -- Assume x ≠ -4 ∧ x ≠ -2, prove x ^ 2 + 6 * x + 8 ≠ 0
    rintro ⟨h1, h2⟩
    by_contra h
    have h3 : x^2 + 6 * x + 8 = 0 := by
      simpa using h
    have h4 : (x + 4) * (x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case x + 4 = 0, so x = -4, contradicts h1.
      have h7 : x = -4 := by
        linarith
      contradiction
    · -- Case x + 2 = 0, so x = -2, contradicts h2.
      have h8 : x = -2 := by
        linarith
      contradiction