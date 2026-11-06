import Mathlib

/- Two complementary angles, A and B, have measures in the ratio of 7 to 23, respectively. What is the ratio of the measure of the complement of angle A to the measure of the complement of angle B? Express your answer as a common fraction. -/
theorem algebra_21136 {A B : ℝ} (hA : A ∈ Set.Ioo 0 π) (hB : B ∈ Set.Ioo 0 π)
    (hAB : A + B = π) (hA' : A / B = 7 / 23) :
    (π - A) / (π - B) = 23 / 7 := by
  -- π - A is B and π - B is A. so answer is reciprocal of A to B
  have hh1: π - A = B := by linarith [hAB]
  have hh2: π - B = A := by linarith [hAB]
  have hh3: B/A = (A/B)⁻¹ := by field_simp [hA, hB]
  rw [hh1, hh2, hh3, hA']; simp