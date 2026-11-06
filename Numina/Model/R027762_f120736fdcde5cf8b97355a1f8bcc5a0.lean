import Mathlib

theorem algebra_179123 : 1 / Real.sin (Real.pi / 18) - Real.sqrt 3 / Real.cos (Real.pi / 18) = 4 := by
  have h1 : Real.sin (Real.pi / 18) > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [show 0 < Real.pi / 18 by linarith [Real.pi_pos]]
    · linarith [show Real.pi / 18 < Real.pi by linarith [Real.pi_pos]]
  have h2 : Real.cos (Real.pi / 18) > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · linarith [show 0 < Real.pi / 18 by linarith [Real.pi_pos]]
    · linarith [show Real.pi - Real.pi / 18 > Real.pi / 18 by linarith [Real.pi_pos]]
  have h3 : Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18) > 0 := by
    nlinarith [h1, h2]
  have eq1 : 1 / Real.sin (Real.pi / 18) - Real.sqrt 3 / Real.cos (Real.pi / 18) =
          (Real.cos (Real.pi / 18) - Real.sqrt 3 * Real.sin (Real.pi / 18)) / (Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18)) := by
    field_simp [show Real.sin (Real.pi / 18) ≠ 0 by linarith, show Real.cos (Real.pi / 18) ≠ 0 by linarith]
    <;> ring
  rw [eq1]
  have eq2 : Real.cos (Real.pi / 18) - Real.sqrt 3 * Real.sin (Real.pi / 18) = 2 * Real.cos (7 * Real.pi / 18) := by
    have h4 : Real.cos (7 * Real.pi / 18) = Real.cos (Real.pi / 18 + Real.pi / 3) := by
      ring_nf
    rw [h4]
    have h5 : Real.cos (Real.pi / 18 + Real.pi / 3) = Real.cos (Real.pi / 18) * Real.cos (Real.pi / 3) - Real.sin (Real.pi / 18) * Real.sin (Real.pi / 3) := by
      rw [Real.cos_add]
    rw [h5]
    have h6 : Real.cos (Real.pi / 3) = 1 / 2 := by
      exact Real.cos_pi_div_three
    have h7 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      exact Real.sin_pi_div_three
    rw [h6, h7]
    ring_nf
  have eq3 : Real.cos (7 * Real.pi / 18) = Real.sin (Real.pi / 9) := by
    have h8 : 7 * Real.pi / 18 = Real.pi / 2 - Real.pi / 9 := by
      linarith [Real.pi_pos]
    rw [h8]
    have h9 : Real.cos (Real.pi / 2 - Real.pi / 9) = Real.sin (Real.pi / 9) := by
      rw [Real.cos_pi_div_two_sub]
    rw [h9]
  have eq4 : Real.sin (Real.pi / 9) = 2 * Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18) := by
    have h10 : Real.sin (Real.pi / 9) = Real.sin (2 * (Real.pi / 18)) := by
      ring_nf
    rw [h10]
    have h11 : Real.sin (2 * (Real.pi / 18)) = 2 * Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18) := by
      rw [Real.sin_two_mul]
    rw [h11]
  have eq5 : Real.cos (Real.pi / 18) - Real.sqrt 3 * Real.sin (Real.pi / 18) = 4 * (Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18)) := by
    rw [eq2, eq3, eq4]
    ring
  rw [eq5]
  have h4 : Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18) > 0 := h3
  field_simp [show Real.sin (Real.pi / 18) * Real.cos (Real.pi / 18) ≠ 0 by linarith [h3]]
  <;> nlinarith