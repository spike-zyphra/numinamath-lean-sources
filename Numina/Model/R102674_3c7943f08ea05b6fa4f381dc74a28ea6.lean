import Mathlib

open Real Set
open scoped Real

theorem algebra_94982 (x : ℝ) (hx : x = 18 * π / 180) :
    sin (2 * x) * sin (3 * x) = cos (2 * x) * cos (3 * x) := by 
  rw [hx]

  have h1 : 2 * (18 * π / 180) = π / 5 := by
    linarith [Real.pi_pos]
  have h2 : 3 * (18 * π / 180) = 3 * π / 10 := by
    linarith [Real.pi_pos]
  rw [h1, h2]

  have h3 : cos (π / 5) * cos (3 * π / 10) - sin (π / 5) * sin (3 * π / 10) = 0 := by 
    have h4 : cos (π / 5) * cos (3 * π / 10) - sin (π / 5) * sin (3 * π / 10) = cos (π / 5 + 3 * π / 10) := by 
      rw [cos_add]
      <;> ring_nf <;> simp [sin_add, cos_add]
      <;> ring_nf

    rw [h4]

    have h5 : π / 5 + 3 * π / 10 = π / 2 := by 
      linarith [Real.pi_pos]

    rw [h5]

    simp

  linarith [h3]
  <;> ring_nf <;> simp [Real.sin_pos_of_pos_of_lt_pi, Real.cos_pos_of_mem_Ioo]
  <;> ring_nf <;> linarith [Real.pi_pos]
  all_goals linarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 5 by linarith [Real.pi_pos] ) (show π / 5 < Real.pi by linarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < 3 * π / 10 by linarith [Real.pi_pos] ) (show 3 * π / 10 < Real.pi by linarith [Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show π / 5 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show 3 * π / 10 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos]), Real.pi_pos]

  all_goals try linarith [Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 5 by linarith [Real.pi_pos] ) (show π / 5 < Real.pi by linarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < 3 * π / 10 by linarith [Real.pi_pos] ) (show 3 * π / 10 < Real.pi by linarith [Real.pi_pos]), Real.pi_pos]

  all_goals try linarith [Real.pi_pos, Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 5 by linarith [Real.pi_pos] ) (show π / 5 < Real.pi by linarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < 3 * π / 10 by linarith [Real.pi_pos] ) (show 3 * π / 10 < Real.pi by linarith [Real.pi_pos]), Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 2 by linarith [Real.pi_pos] ) (show π / 2 < Real.pi by linarith [Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show π / 5 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos]), Real.cos_pos_of_mem_Ioo (show 3 * π / 10 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [Real.pi_pos]), mul_pos (Real.sin_pos_of_pos_of_lt_pi (show 0 < π / 5 by linarith [Real.pi_pos] ) (show π / 5 < Real.pi by linarith [Real.pi_pos])) (Real.sin_pos_of_pos_of_lt_pi (show 0 < 3 * π / 10 by linarith [Real.pi_pos] ) (show 3 * π / 10 < Real.pi by linarith [Real.pi_pos] ) ) ]
  <;> try ring_nf
  <;> try simp [Real.sin_add, Real.cos_add]
  <;> try linarith [Real.pi_pos]