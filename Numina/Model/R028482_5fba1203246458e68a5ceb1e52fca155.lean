import Mathlib

open Real Set
open scoped Real

theorem algebra_163610 (α : Real) :
  1 - cos (π - 8 * α) - cos (π + 4 * α) =
  4 * cos (4 * α) * cos (2 * α + π / 6) * cos (2 * α - π / 6) := by
  have h1 : cos (π - 8 * α) = -cos (8 * α) := by
    rw [cos_pi_sub]
  have h2 : cos (π + 4 * α) = -cos (4 * α) := by
    rw [cos_add]
    simp [cos_pi, sin_pi]
    all_goals ring
  rw [h1, h2]
  have h3 : 1 - (-cos (8 * α)) - (-cos (4 * α)) =
      1 + cos (8 * α) + cos (4 * α) := by ring
  rw [h3]
  have h4 : cos (8 * α) = 2 * cos (4 * α) ^ 2 - 1 := by
    have h8 : cos (8 * α) = cos (2 * (4 * α)) := by
      ring_nf
    rw [h8]
    rw [cos_two_mul]
    all_goals ring_nf <;> simp [cos_sq]
  have eq3 : 1 + cos (8 * α) + cos (4 * α) = 2 * cos (4 * α) ^ 2 + cos (4 * α) := by
    rw [h4]
    all_goals ring_nf <;> simp [cos_sq]
    all_goals ring
  rw [eq3]
  have h5 : cos (2 * α + π / 6) * cos (2 * α - π / 6) =
      (1 / 2) * (cos (4 * α) + Real.cos (Real.pi / 3)) := by
    have h6 : cos (2 * α + π / 6) * cos (2 * α - π / 6) =
        (1 / 2) * (cos (4 * α) + cos (Real.pi / 3)) := by
      have h7 : cos (2 * α + π / 6) * cos (2 * α - π / 6) =
          (1 / 2) * (cos ((2 * α + π / 6) + (2 * α - π / 6)) + cos ((2 * α + π / 6) - (2 * α - π / 6)) ) := by
        rw [cos_add_cos]
        all_goals ring_nf
        <;> simp [cos_add, cos_sub]
        <;> ring_nf
      have h8 : (2 * α + π / 6 : ℝ) + (2 * α - π / 6) = 4 * α := by
        ring_nf
      have h9 : (2 * α + π / 6 : ℝ) - (2 * α - π / 6) = Real.pi / 3 := by
        ring_nf
      rw [h8] at h7
      rw [h9] at h7
      linarith
    rw [h6]
    <;> ring_nf <;> simp [Real.cos_pi_div_three]
    all_goals linarith
  have h6' : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have eq7 : 4 * cos (4 * α) * cos (2 * α + π / 6) * cos (2 * α - π / 6) =
      2 * cos (4 * α) ^ 2 + cos (4 * α) := by
    calc
      4 * cos (4 * α) * cos (2 * α + π / 6) * cos (2 * α - π / 6)
        = 4 * cos (4 * α) * (cos (2 * α + π / 6) * cos (2 * α - π / 6)) := by ring
      _ = 4 * cos (4 * α) * ( (1 / 2) * (cos (4 * α) + (1 / 2) ) ) := by
        rw [h5, h6']
        <;> ring_nf <;> simp [Real.cos_pi_div_three]
      _ = 2 * cos (4 * α) ^ 2 + cos (4 * α) := by
        ring_nf
        <;> simp [Real.cos_pi_div_three]
        <;> ring_nf <;> linarith
  rw [eq7]
  all_goals ring_nf <;> simp [Real.cos_pi_div_three]
  all_goals ring
  all_goals simp [Real.cos_pi_div_three] <;> ring