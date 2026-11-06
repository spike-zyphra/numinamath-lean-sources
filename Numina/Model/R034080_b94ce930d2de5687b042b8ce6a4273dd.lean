import Mathlib
open Real

theorem algebra_879 {x y z : ℝ} (h₀ : x < 0) (h₁ : 0 < z) (h₂ : x * y > 0)
    (h₃ : |y| > |z|) (h₄ : |z| > |x|) :
    |x + z| + |y + z| - |x - y| = 0 := by

  have h5 : y < 0 := by
    have h6 : x * y > 0 := h₂
    apply mul_pos_iff.mp at h6
    cases h6 with
    | inl h7 =>
      linarith
    | inr h8 =>
      linarith

  have h6 : |x| = -x := by
    rw [abs_of_neg h₀]

  have h7 : |z| = z := by
    rw [abs_of_pos h₁]

  have h8 : |y| = -y := by
    rw [abs_of_neg h5]

  have h9 : y < -z := by
    linarith [h₃, h8, h7]

  have h10 : x + z > 0 := by
    linarith [h₄, h7, h6]

  have h11 : |x + z| = x + z := by
    rw [abs_of_pos h10]

  have h12 : y + z < 0 := by
    nlinarith

  have h13 : |y + z| = - (y + z) := by
    rw [abs_of_neg h12]

  have h14 : x - y > 0 := by
    nlinarith

  have h15 : |x - y| = x - y := by
    rw [abs_of_pos h14]

  rw [h11, h13, h15]
  linarith