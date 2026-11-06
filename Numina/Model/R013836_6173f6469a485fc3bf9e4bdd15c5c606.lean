import Mathlib

open Real Set
open scoped Real

theorem algebra_106993 : tan (π / 9) + 4 * sin (π / 9) = sqrt 3 := by
  have h1 : tan (π / 9) = sin (π / 9) / cos (π / 9) := by
    rw [tan_eq_sin_div_cos]

  rw [h1]
  have h2 : sin (π / 9) ^ 2 + cos (π / 9) ^ 2 = 1 := by
    exact Real.sin_sq_add_cos_sq (π / 9)
  have h5 : sin (3 * (π / 9)) = Real.sqrt 3 / 2 := by
    have h51 : 3 * (π / 9) = π / 3 := by ring
    rw [h51]
    rw [sin_pi_div_three]

  have h6 : cos (3 * (π / 9)) = 1 / 2 := by
    have h61 : 3 * (π / 9) = π / 3 := by ring
    rw [h61]
    rw [cos_pi_div_three]

  have eq1 : 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 = Real.sqrt 3 / 2 := by
    have h3 : sin (3 * (π / 9)) = 3 * sin (π / 9) - 4 * sin (π / 9) ^ 3 := by
      rw [sin_three_mul]
    rw [h3] at h5
    linarith [h5, Real.sqrt_nonneg 3]

  have eq2 : 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) = 1 / 2 := by
    have h4 : cos (3 * (π / 9)) = 4 * cos (π / 9) ^ 3 - 3 * cos (π / 9) := by
      rw [cos_three_mul]
    rw [h4] at h6
    linarith [h6]

  have h8 : sin (π / 9) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h9 : cos (π / 9) > 0 := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have h10 : sin (π / 9) + 4 * sin (π / 9) * cos (π / 9) = Real.sqrt 3 * cos (π / 9) := by
    have h11 : sin (2 * (π / 9)) = 2 * sin (π / 9) * cos (π / 9) := by
      rw [sin_two_mul]
    have eq3 : sin (2 * (π / 9)) = Real.sqrt 3 / 2 * cos (π / 9) - 1 / 2 * sin (π / 9) := by
      have anglesin : sin (π / 3) = Real.sqrt 3 / 2 := by
        rw [sin_pi_div_three]
      have anglecos : cos (π / 3) = 1 / 2 := by
        rw [cos_pi_div_three]
      have eq31 : sin (2 * (π / 9)) = sin (π / 3 - (π / 9)) := by
        ring_nf
      have eq32 : sin (π / 3 - (π / 9)) = sin (π / 3) * cos (π / 9) - cos (π / 3) * sin (π / 9) := by
        rw [sin_sub]
      rw [eq31, eq32, anglesin, anglecos]
    calc
      sin (π / 9) + 4 * sin (π / 9) * cos (π / 9)
        = sin (π / 9) + 2 * (2 * sin (π / 9) * cos (π / 9)) := by ring
      _ = sin (π / 9) + 2 * sin (2 * (π / 9)) := by
        rw [show 2 * sin (π / 9) * cos (π / 9) = sin (2 * (π / 9)) by rw [sin_two_mul]]
      _ = sin (π / 9) + 2 * (Real.sqrt 3 / 2 * cos (π / 9) - 1 / 2 * sin (π / 9)) := by
        rw [eq3]
      _ = Real.sqrt 3 * cos (π / 9) := by
        ring_nf <;> nlinarith [h2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0: ℝ) ≤ (3) by norm_num)]
  have eq0 : sin (π / 9) / cos (π / 9) + 4 * sin (π / 9) = (sin (π / 9) + 4 * sin (π / 9) * cos (π / 9)) / cos (π / 9) := by
    field_simp
    <;> ring_nf
    <;> field_simp
  rw [eq0]
  rw [h10]
  <;> field_simp [h9]
  <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0: ℝ) ≤ (3) by norm_num)]