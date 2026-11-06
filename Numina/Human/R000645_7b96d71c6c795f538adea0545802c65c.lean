import Mathlib

/- At the Hardey Fitness Center, the management did a survey of their membership. The average age of the female members was 40 years old. The average age of the male members was 25 years old. The average age of the entire membership was 30 years old. What is the ratio of the female to male members? Express your answer as a common fraction. -/
theorem algebra_13588 {f m : ℕ} (hf : f > 0) (hm : m > 0)
    (h₁ : (f * 40 + m * 25 : ℚ) / (f + m) = 30) :
    (f / m : ℚ) = 1 / 2 := by
  qify at *
  field_simp at h₁ ⊢
  linarith
