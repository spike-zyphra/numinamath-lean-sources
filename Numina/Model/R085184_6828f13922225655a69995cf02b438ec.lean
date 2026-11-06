import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_238058 {f : ℝ → ℝ}
  (hf : f = λ x => 8 * sin x ^ 2 * cos x ^ 2 - 2 * cos (2 * x) ^ 2) :
  IsLeast {T | 0 < T ∧ f = λ x => f (x + T)} (Real.pi / 2) := by
  constructor
  · -- Show that π/2 is a positive period
    constructor
    · -- Show π/2 > 0
      positivity
    · -- Show f = fun x ↦ f (x + π / 2)
      funext x
      rw [hf]
      have h1 : 8 * sin (x + Real.pi / 2) ^ 2 * cos (x + Real.pi / 2) ^ 2 - 2 * cos (2 * (x + Real.pi / 2)) ^ 2 =
          8 * sin x ^ 2 * cos x ^ 2 - 2 * cos (2 * x) ^ 2 := by
        have h2 : sin (x + Real.pi / 2) = cos x := by
          rw [sin_add, sin_pi_div_two, cos_pi_div_two]
          ring
        have h3 : cos (x + Real.pi / 2) = -sin x := by
          rw [cos_add, sin_pi_div_two, cos_pi_div_two]
          ring
        have h4 : cos (2 * (x + Real.pi / 2)) = -cos (2 * x) := by
          have h5 : 2 * (x + Real.pi / 2) = 2 * x + Real.pi := by ring
          rw [h5]
          have h6 : cos (2 * x + Real.pi) = -cos (2 * x) := by
            rw [cos_add, cos_pi, sin_pi]
            ring
          linarith
        rw [h2, h3, h4]
        all_goals ring_nf
        <;> simp [Real.sin_sq, Real.cos_sq] <;> ring
      simpa [h1]
  · -- Show there is no positive period less than π/2
    intro T hT
    rcases hT with ⟨hT_pos, hT_period⟩
    by_contra h
    push_neg at h
    have h1 := congr_fun hT_period 0
    simp [hf] at h1
    have h2 := congr_fun hT_period (Real.pi / 4)
    simp [hf] at h2
    have h3 : Real.sin (2 * T) = 0 := by
      have h4 : Real.sin (2 * T) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq T, Real.sin_sq_add_cos_sq (2 * T), Real.sin_two_mul T, Real.sin_two_mul (Real.pi / 4 + T), Real.cos_pi_div_two, Real.sin_pi_div_two]
      linarith
    have h5 : 2 * T > 0 := by linarith [hT_pos]
    have h6 : Real.sin (2 * T) > 0 := by
      apply Real.sin_pos_of_pos_of_lt_pi
      linarith
      linarith [show 2 * T < Real.pi by linarith [show Real.pi / 2 > 0 by positivity, show Real.pi > 0 by positivity]]
    linarith [h3, h6]