import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11346 {f : ℝ → ℝ}
  (hf : f = λ x => cos (x / 2) * sqrt 3 * sin (x / 2) + (-1) * (cos (x / 2))^2 + 1)
  (x : ℝ) (hx : x ∈ Icc 0 (π / 2)) (h : f x = 11 / 10) :
  cos x = (4 * sqrt 3 - 3) / 10 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : f x = cos (x / 2) * sqrt 3 * sin (x / 2) + (-1) * (cos (x / 2))^2 + 1 := by
    rw [hf]
  rw [h1] at h
  have eq2 : cos (x / 2) * sqrt 3 * sin (x / 2) - (cos (x / 2))^2 = 1 / 10 := by
    linarith
  have h2 : sin x = 2 * sin (x / 2) * cos (x / 2) := by 
    rw [←sin_two_mul]
    ring_nf
  have h3 : cos x = 2 * (cos (x / 2))^2 - 1 := by
    have h3 : cos x = cos (2 * (x / 2)) := by ring_nf
    rw [h3]
    rw [cos_two_mul]
  have eq4 : sqrt 3 * sin x / 2 - (1 + cos x) / 2 = 1 / 10 := by
    have h5 : sqrt 3 * cos (x / 2) * sin (x / 2) = sqrt 3 * sin x / 2 := by
      calc 
        sqrt 3 * cos (x / 2) * sin (x / 2) = sqrt 3 * (cos (x / 2) * sin (x / 2)) := by ring
        _ = sqrt 3 * (sin x / 2) := by
            rw [show cos (x / 2) * sin (x / 2) = sin x / 2 by
              have h6 : sin x = 2 * sin (x / 2) * cos (x / 2) := by
                rw [←sin_two_mul]
                ring_nf
              linarith
            ]
        _ = sqrt 3 * sin x / 2 := by ring
    have h6 : (cos (x / 2))^2 = (1 + cos x) / 2 := by
      have h3' : cos x = 2 * (cos (x / 2))^2 - 1 := h3
      linarith
    have eq3 : cos (x / 2) * sqrt 3 * sin (x / 2) - (cos (x / 2))^2 = 1 / 10 := by
      linarith [eq2]
    linarith [eq3, h5, h6]
  -- Multiply through to clear denominator
  have eq5 : sqrt 3 * sin x - (1 + cos x) = 1 / 5 := by
    linarith [eq4]
  -- Rearrange to solve
  have eq6 : sqrt 3 * sin x - cos x = 6 / 5 := by
    linarith [eq5]
  have eq7 : sqrt 3 * sin x - cos x = 2 * sin (x - Real.pi / 6) := by
    rw [Real.sin_sub, Real.sin_pi_div_six, Real.cos_pi_div_six]
    ring_nf
  have h8 : sin (x - Real.pi / 6) = 3 / 5 := by
    linarith [eq6, eq7]
  -- Show x - π/6 in range where sin is injective
  have h9 : cos (x - Real.pi / 6) ≥ 0 := by
    have h10 : x - Real.pi / 6 ≥ - Real.pi / 6 := by
      linarith [show Real.pi / 6 ≥ 0 by nlinarith [Real.pi_pos]]
    have h11 : x - Real.pi / 6 ≤ Real.pi / 3 := by
      nlinarith [Real.pi_pos, hx2]
    have h12 : cos (x - Real.pi / 6) ≥ 0 := by
      apply cos_nonneg_of_neg_pi_div_two_le_of_le 
      linarith
      linarith
    exact h12
  have h10 : cos (x - Real.pi / 6) = 4 / 5 := by
    have h11 : cos (x - Real.pi / 6) ^ 2 + sin (x - Real.pi / 6) ^ 2 = 1 := Real.cos_sq_add_sin_sq (x - Real.pi / 6)
    rw [h8] at h11
    nlinarith [h11, h9]
  have h12 : cos x = cos (Real.pi / 6) * cos (x - Real.pi / 6) - sin (Real.pi / 6) * sin (x - Real.pi / 6) := by
    rw [← Real.cos_add]
    ring_nf
  rw [h12]
  rw [h10, h8]
  have h13 : cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
  have h14 : sin (Real.pi / 6) = 1 / 2 := Real.sin_pi_div_six
  rw [h13, h14]
  field_simp
  ring_nf