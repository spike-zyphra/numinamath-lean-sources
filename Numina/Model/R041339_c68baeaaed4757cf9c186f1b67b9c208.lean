import Mathlib
open Real

theorem algebra_95315 {r1 r2 h1 h2 : ℝ} (hr1 : r1 > 0) (hr2 : r2 > 0)
(hvol : π * r1^2 * h1 = π * r2^2 * h2) (hrr : r2 = 1.1 * r1) :
h1 = 121 / 100 * h2 := by
  rw [hrr] at hvol 
  have eq1 : π * r1 ^ 2 * h1 = π * (1.21 * (r1 ^ 2) ) * h2 := by
    ring_nf at hvol ⊢ 
    <;> nlinarith 
  have hpi_ne_zero : π ≠ 0 := by
    linarith [Real.pi_pos]

  have eq2 : r1 ^ 2 * h1 = 1.21 * (r1 ^ 2) * h2 := by
    apply (mul_left_inj' hpi_ne_zero).mp 
    linarith [eq1]

  have hr1_sq_ne_zero : r1 ^ 2 ≠ 0 := by
    nlinarith 
  have eq3 : h1 = 1.21 * h2 := by 
    apply (mul_left_inj' hr1_sq_ne_zero).mp 
    linarith [eq2]

  rw [eq3]
  ring_nf