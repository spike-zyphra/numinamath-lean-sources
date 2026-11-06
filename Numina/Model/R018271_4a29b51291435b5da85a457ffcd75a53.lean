import Mathlib

theorem algebra_278619 {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x)
    (hper : ∀ x, f (x + Real.pi) = f x) (hsin : ∀ x ∈ Set.Icc 0 (Real.pi / 2), f x = Real.sin x) :
    f (5 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h1 : f (5 * Real.pi / 3) = f (2 * Real.pi / 3) := by
    have h2 : 5 * Real.pi / 3 = (2 * Real.pi / 3) + Real.pi := by
      linarith [Real.pi_pos]
    rw [h2]
    rw [show f ((2 * Real.pi / 3) + Real.pi) = f (2 * Real.pi / 3) by rw [hper]]
  have h2 : f (2 * Real.pi / 3) = f (- (Real.pi / 3)) := by
    have h3 : 2 * Real.pi / 3 = (- (Real.pi / 3)) + Real.pi := by
      linarith [Real.pi_pos]
    rw [h3]
    rw [show f ((- (Real.pi / 3)) + Real.pi) = f (- (Real.pi / 3)) by rw [hper]]
  have h3 : f (- (Real.pi / 3)) = f (Real.pi / 3) := by
    have hf_pi3 := hf (Real.pi / 3)
    linarith [hf_pi3]
  have h4 : f (Real.pi / 3) = Real.sin (Real.pi / 3) := by 
    apply hsin
    constructor
    · -- 0 ≤ π/3
      linarith [Real.pi_pos]
    · -- π/3 ≤ π/2
      linarith [Real.pi_pos]
  have h5 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := Real.sin_pi_div_three
  rw [h1, h2, h3, h4, h5]