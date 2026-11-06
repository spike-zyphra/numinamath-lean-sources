import Mathlib

open Real Set
open scoped Real

theorem algebra_319580 (x y : ℝ) (hx : 0 < x) (hy : x < y) (hyy : y < π / 2)
  (P : ℝ) (hP : P = cos (2 * x) - cos (2 * y) - 4 * cos x + 4 * cos y) :
  P ∈ Ioo (-2) 0 := by
  have h1 : 0 < x := hx
  have h2 : x < y := hy
  have h3 : y < π / 2 := hyy
  have hcos1 : cos x > cos y := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    all_goals linarith [Real.pi_pos]
  have hcosx : 0 < cos x := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hcosy : 0 < cos y := by
    apply cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hcosx_lt_one : cos x < 1 := by
    have h4 : cos x < cos (0 : ℝ) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    have h5 : cos (0 : ℝ) = 1 := Real.cos_zero
    linarith [h4, h5]
  have h6 : cos (2 * x) = 2 * (cos x)^2 - 1 := by
    rw [cos_two_mul]
    all_goals try nlinarith
  have h7 : cos (2 * y) = 2 * (cos y)^2 - 1 := by
    rw [cos_two_mul]
    all_goals try nlinarith
  have hP' : P = 2 * (cos x ^ 2 - cos y ^ 2) - 4 * (cos x - cos y) := by
    rw [hP, h6, h7]
    ring_nf
  have hP'' : P = 2 * (cos x - cos y) * (cos x + cos y - 2) := by
    rw [hP']
    nlinarith [hcos1]
  constructor
  · -- Show that -2 < P
    rw [hP'']
    have h10 : 0 < cos x - cos y := by linarith
    have h11 : cos x + cos y - 2 < 0 := by
      nlinarith [hcosx, hcosy, hcosx_lt_one]
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 1 - cos x by nlinarith [Real.cos_le_one x, hcosx_lt_one]), sq_pos_of_pos hcosy, sq_pos_of_pos hcosx, sq_pos_of_pos (show 0 < 1 - cos y by nlinarith [Real.cos_le_one y]), mul_pos (show (0 : ℝ) < 1 - cos x by nlinarith [Real.cos_le_one x, hcosx_lt_one]) hcosy, mul_pos hcosx (show (0 : ℝ) < 1 - cos y by nlinarith [Real.cos_le_one y]), Real.sin_pos_of_pos_of_lt_pi (show 0 < x by linarith [Real.pi_pos]) (show x < Real.pi by linarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < y by linarith [Real.pi_pos]) (show y < Real.pi by linarith [Real.pi_pos])]
  · -- Show that P < 0
    rw [hP'']
    have h9 : cos x - cos y > 0 := by linarith
    have h10 : cos x + cos y - 2 < 0 := by
      nlinarith [hcosx, hcosy, hcosx_lt_one]
    nlinarith