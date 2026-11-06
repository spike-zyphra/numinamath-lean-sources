import Mathlib

open Real Set
open scoped Real

theorem algebra_107269 (x : Real) (hx : x ∈ Ioo 0 (π/2)) :
    sin x - 2 * cos x + 32 / (125 * sin x * (1 - cos x)) ∈ Ici (2/5) := by 
  rcases hx with ⟨hx1, hx2⟩
  have hx3 : sin x > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [hx1, hx2, Real.pi_pos]
    linarith [hx1, hx2, Real.pi_pos]
  have hx4 : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [hx1, hx2, Real.pi_pos]
  have hx6 : 1 - cos x > 0 := by
    have hcos : cos x < 1 := by
      have h1 : x > 0 := hx1
      have h2 : x < Real.pi / 2 := hx2
      have h3 : sin x > 0 := by
        apply sin_pos_of_pos_of_lt_pi
        linarith [h1, h2, Real.pi_pos]
        linarith [h1, h2, Real.pi_pos]
      have h4 : cos x < cos (0 : ℝ) := by 
        apply Real.cos_lt_cos_of_nonneg_of_le_pi
        all_goals linarith [h1, h2, Real.pi_pos]
      have h5 : cos (0 : ℝ) = 1 := Real.cos_zero
      linarith [h4, h5]
    linarith
  have h14 : sin x * (1 - cos x) > 0 := mul_pos hx3 hx6
  have h34 : (sin x - 2 * cos x + 32 / (125 * sin x * (1 - cos x)) ) - 2 / 5 ≥ 0 := by
    have h4 : ((sin x - 2 * cos x + 32 / (125 * sin x * (1 - cos x)) ) - 2 / 5) = ((sin x - 2 * cos x) * (125 * sin x * (1 - cos x)) + 32 - (2 / 5) * (125 * sin x * (1 - cos x)) ) / (125 * sin x * (1 - cos x)) := by 
      field_simp
      ring
    rw [h4]
    have hx7 : (125 * sin x * (1 - cos x)) > 0 := by positivity
    have h55 : (sin x - 2 * cos x) * (125 * sin x * (1 - cos x)) + 32 - (2 / 5) * (125 * sin x * (1 - cos x)) ≥ 0 := by
      nlinarith [sq_nonneg (sin x - 2 / 5), sq_nonneg (cos x - 3 / 5), sq_nonneg (sin x - 2 * cos x + 11 / 25), 
          sq_nonneg (sin x * (1 - cos x) - 1 / 125), 
          sq_nonneg (sin x - 2 / 5), sq_nonneg (cos x - 3 / 5), 
          Real.sin_sq_add_cos_sq x, 
          mul_pos hx3 hx6, 
          mul_pos hx3 hx4, 
          sq_nonneg (sin x^2 + cos x^2 - 1)
        ]
    apply div_nonneg 
    linarith
    positivity
  have hx11 : sin x - 2 * cos x + 32 / (125 * sin x * (1 - cos x)) ≥ 2 / 5 := by linarith
  simp at *
  linarith [hx11]