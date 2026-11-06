import Mathlib

open Real

theorem algebra_254774 {a b : ℝ × ℝ}
    (ha : a = (1, 1)) (hb : b = ((1 - sqrt 3) / 2, (1 + sqrt 3) / 2)) :
    b = (a.1 * cos (π / 3) - a.2 * sin (π / 3), a.1 * sin (π / 3) + a.2 * cos (π / 3)) := by
  rw [ha, hb]
  have hcos : cos (Real.pi / 3) = 1 / 2 := by
    exact cos_pi_div_three
  have hsin : sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
    exact sin_pi_div_three
  simp [hcos, hsin]
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt, mul_add, mul_comm, mul_assoc, sq]
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt, mul_add, mul_comm, mul_assoc, sq]
  <;> try { simp [Real.sq_sqrt, mul_add, mul_comm, mul_assoc, sq] }
  <;> try { tauto }
  <;> try { rfl }