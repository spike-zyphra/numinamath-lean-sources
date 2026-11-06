import Mathlib

theorem algebra_8011 {k : ℝ} : (∃ x, 1988*x^2+k*x+8891=0 ∧ 8891*x^2+k*x+1988=0) ↔ k=-10879 ∨ k=10879 := by
  constructor
  · -- Forward direction: if there's a common root, then k is either -10879 or 10879
    rintro ⟨x, h₁, h₂⟩
    have h3 : 6903 * x^2 = 6903 := by
      nlinarith 
    have h4 : x^2 = 1 := by
      nlinarith
    have h5 : x = 1 ∨ x = -1 := by
      rw [sq_eq_one_iff] at h4
      tauto
    cases h5 with
    | inl h6 =>
      rw [h6] at h₁
      left
      linarith 
    | inr h6 =>
      rw [h6] at h₁
      right
      linarith
  · -- Backward direction: if k is either -10879 or 10879, then there's a common root
    rintro (h | h)
    · -- Case k = -10879, x = 1
      rw [h]
      use 1
      constructor
      · -- Check first polynomial
        norm_num
      · -- Check second polynomial
        norm_num 
    · -- Case k = 10879, x = -1
      rw [h]
      use -1 
      constructor
      · -- Check first polynomial
        norm_num
      · -- Check second polynomial
        norm_num