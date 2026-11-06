import Mathlib

theorem algebra_21443 : {x : ℝ | x^2 - 9 * x - 52 ≠ 0 ∧ |x - 13| / (x^2 - 9 * x - 52) ≤ 0} = Set.Ioo (-4) 13 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · -- Assume h : x in the solution set
    intro h
    rcases h with ⟨hx1, hx2⟩
    have h1 : x ^ 2 - 9 * x - 52 < (0 : ℝ) := by
      by_contra h'
      push_neg at h'
      by_cases h3 : x ^ 2 - 9 * x - 52 > (0 : ℝ)
      · -- Case where the denominator is greater than 0
        have h4 : |x - 13| = (0 : ℝ) := by
          have h5 : |x - 13| / (x^2 - 9 * x - 52) ≤ (0 : ℝ) := by linarith [hx2]
          have h6 : |x - 13| / (x^2 - 9 * x - 52) ≥ (0 : ℝ) := by
            apply div_nonneg
            · -- Show |x - 13| ≥ 0
              positivity
            · -- Show x^2 - 9 * x - 52 ≥ 0
              linarith
          have h7 : |x - 13| / (x^2 - 9 * x - 52) = (0 : ℝ) := by linarith [h5, h6]
          have h8 : |x - 13| = (0 : ℝ) := by
            have hx9 : x ^ 2 - 9 * x - 52 ≠ 0 := by linarith [h3]
            have hx8 : |x - 13| = (0 : ℝ) := by
              field_simp at h7 ⊢
              <;> nlinarith [abs_nonneg (x - 13)]
            exact hx8
          exact h8
        have hx13 : x = (13 : ℝ) := by
          rw [abs_eq_zero] at h4
          linarith
        have hx14 : x ^ 2 - 9 * x - 52 = (0 : ℝ) := by
          rw [hx13]
          norm_num
        linarith -- Contradicts h3
      · -- Case where the denominator is equal to 0 (contradicts hx1)
        have h4 : x ^ 2 - 9 * x - 52 = (0 : ℝ) := by
          linarith
        tauto
    have h2 : -4 < x := by nlinarith
    have h3 : x < 13 := by nlinarith
    constructor <;> linarith
  · -- Assume h : x ∈ (-4, 13)
    rintro ⟨h1, h2⟩
    constructor
    · -- Show x^2 - 9 * x - 52 ≠ 0
      have h3 : x^2 - 9 * x - 52 < (0 : ℝ) := by nlinarith
      have h4 : x^2 - 9 * x - 52 ≠ 0 := by
        nlinarith
      exact h4
    · -- Show |x - 13| / (x^2 - 9 * x - 52) ≤ 0
      have h3 : x^2 - 9 * x - 52 < (0 : ℝ) := by nlinarith
      have h4 : |x - 13| ≥ (0 : ℝ) := by apply abs_nonneg
      apply div_nonpos_of_nonneg_of_nonpos
      · -- Show |x - 13| ≥ 0
        positivity
      · -- Show x^2 - 9 * x - 52 ≤ 0
        linarith