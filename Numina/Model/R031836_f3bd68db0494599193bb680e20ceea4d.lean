import Mathlib

open Real

theorem algebra_9205 (k : ℤ) {f : ℝ → ℝ} (hf : f = λ x => 2 + 3 * sin x) :
    MonotoneOn f {x | -(π/2) + 2*k*π ≤ x ∧ x ≤ π/2 + 2*k*π} := by
  intros x hx y hy hxy
  have hx1 : -(π / 2) + 2 * k * π ≤ x := hx.1
  have hy1 : -(π / 2) + 2 * k * π ≤ y := hy.1
  have hx2 : x ≤ π / 2 + 2 * k * π := hx.2
  have hy2 : y ≤ π / 2 + 2 * k * π := hy.2
  have h1 : -π / 2 ≤ x - 2 * k * π := by
    linarith
  have h2 : x - 2 * k * π ≤ π / 2 := by
    linarith
  have h3 : -π / 2 ≤ y - 2 * k * π := by
    linarith
  have h4 : y - 2 * k * π ≤ π / 2 := by
    linarith
  have h5 : sin (x - 2 * k * π) ≤ sin (y - 2 * k * π) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two
    all_goals
      ring_nf at *
      <;> linarith
  have h6 : sin (x - 2 * k * π) = sin x := by
    have : x - 2 * k * π = x - k * (2 * π) := by
      ring
    rw [this]
    rw [show sin (x - k * (2 * π)) = sin x by
      rw [sin_sub_int_mul_two_pi]
    ]
  have h7 : sin (y - 2 * k * π) = sin y := by
    have : y - 2 * k * π = y - k * (2 * π) := by
      ring
    rw [this]
    rw [show sin (y - k * (2 * π)) = sin y by
      rw [sin_sub_int_mul_two_pi]
    ]
  have h8 : sin x ≤ sin y := by
    linarith [h5, h6, h7]
  rw [hf]
  simp only
  all_goals
    nlinarith [h8]