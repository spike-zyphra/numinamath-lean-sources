import Mathlib

theorem algebra_184045 {x1 x2 : ℝ} (hx1 : 2*x1^2-9*x1+8=0) (hx2 : 2*x2^2-9*x2+8=0)
    (hroots : x1≠x2) :
    ∃ x3 x4, x3 = 1/(x1+x2) ∧ x4 = (x1-x2)^2 ∧
    36*x3^2-161*x3+34=0 ∧ 36*x4^2-161*x4+34=0 := by

  have h1 : 2 * x1^2 - 9 * x1 + 8 = 0 := hx1
  have h2 : 2 * x2^2 - 9 * x2 + 8 = 0 := hx2
  have hsum : 2 * (x1 + x2) = 9 := by
    have hsub : (x1 - x2) * (2 * (x1 + x2) - 9) = 0 := by
      linarith
    cases (mul_eq_zero.mp hsub) with
    | inl h3 =>
      exfalso
      apply hroots
      linarith
    | inr h4 => 
      linarith
  
  have hsum2 : x1 + x2 = 9/2 := by linarith
  have hprod : x1 * x2 = 4 := by 
    nlinarith
  
  use 1/(x1 + x2)
  use (x1 - x2)^2
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · -- Check the first quadratic equation
    have hr : 1/(x1 + x2) = 2/9 := by
      rw [hsum2]
      norm_num
    rw [hr]
    norm_num
  · -- Check the second quadratic equation
    have hsq : (x1 - x2)^2 = 17/4 := by
      have : (x1 - x2)^2 = (x1 + x2)^2 - 4 * (x1 * x2) := by
        ring_nf
      rw [this, hsum2, hprod]
      nlinarith
    rw [hsq]
    norm_num