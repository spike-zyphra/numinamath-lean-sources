import Mathlib

/-If $-6<\frac{8-2x}{8}≤4$, then x have 40 integer solutions.-/
theorem inequalities_626745 :
    Set.ncard {x : ℤ | -6 < (8 - 2 * (Int.cast x : ℝ)) / 8 ∧ (8 - 2 * (Int.cast x : ℝ)) / 8 ≤ 4} = 40 := by
  -- By some operations on the original inequality, we can show that it is equal to &-12≤x<28&, that is to say &-12≤x≤27&.
  have h₁ : {x : ℤ | -6 < (8 - 2 * (Int.cast x : ℝ)) / 8 ∧ (8 - 2 * (Int.cast x : ℝ)) / 8 ≤ 4} = Finset.Icc (-12) 27 := by
    ext x
    simp
    constructor
    · -- Assume -6 < (8 - 2 * x) / 8 ∧ (8 - 2 * x) / 8 ≤ 4, prove -15 ≤ x ∧ x ≤ 24
      intro h
      rcases h with ⟨h1, h2⟩
      have h11 : 28 > (Int.cast x : ℝ) := by linarith
      norm_cast at h11
      have h12 : x < 27 + 1 := by linarith
      apply Int.le_of_lt_add_one at h12
      have h21 : -12 ≤ (Int.cast x : ℝ) := by linarith
      norm_cast at h21
    · -- Assume -15 ≤ x ∧ x ≤ 24, prove -6 < (8 - 2 * x) / 8 ∧ (8 - 2 * x) / 8 ≤ 4
      rintro ⟨ht1, ht2⟩
      have ht11 : -12 ≤ (Int.cast x : ℝ) := by norm_cast
      have ht12 : (8 - 2 * (Int.cast x : ℝ)) / 8 ≤ 4 := by linarith
      have ht21 : x < 28 := by linarith
      have ht22 : (Int.cast x : ℝ) < 28 := by norm_cast;
      have ht23 : -6 < (8 - 2 * (Int.cast x : ℝ)) / 8 := by linarith
      exact ⟨ht23, ht12⟩
  -- Count the number of integers between -12 and 27, which is 40.
  rw [h₁]
  rw [Set.ncard_coe_Finset]
  native_decide