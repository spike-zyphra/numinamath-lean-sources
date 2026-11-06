import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_245238 : (1 + Real.cos (Real.pi / 7) + I * Real.sin (6 * Real.pi / 7))^14 =
    -2^14 * (Real.cos (Real.pi / 14))^14 := by
  have h1 : Real.sin (6 * Real.pi / 7) = Real.sin (Real.pi / 7) := by
    have h2 : 6 * Real.pi / 7 = Real.pi - Real.pi / 7 := by
      ring
    rw [h2]
    rw [Real.sin_pi_sub]
  rw [h1]
  have h2 : (1 + Real.cos (Real.pi / 7) + I * Real.sin (Real.pi / 7)) =
      2 * Real.cos (Real.pi / 14) * (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) := by
    rw [show Real.pi / 7 = 2 * (Real.pi / 14) by ring]
    have hcos : Real.cos (2 * (Real.pi / 14)) = 2 * (Real.cos (Real.pi / 14)) ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    have hsin : Real.sin (2 * (Real.pi / 14)) = 2 * Real.sin (Real.pi / 14) * Real.cos (Real.pi / 14) := by
      rw [Real.sin_two_mul]
    rw [hcos, hsin]
    ring_nf
    <;> simp [Complex.ext_iff]
    <;> ring_nf
    <;> simp [Complex.ext_iff, Real.sin_sq]
    <;> ring_nf
  rw [h2]
  have eq1 : (2 * Real.cos (Real.pi / 14) * (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14))) ^ 14 =
      (2 * Real.cos (Real.pi / 14)) ^ 14 * (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) ^ 14 := by
    rw [mul_pow]
  rw [eq1]
  have h3 : (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) ^ 14 =
      Real.cos (14 * (Real.pi / 14)) + I * Real.sin (14 * (Real.pi / 14)) := by
    have h1 : ∀ (n : ℕ), (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) ^ n =
        Real.cos (n * (Real.pi / 14)) + I * Real.sin (n * (Real.pi / 14)) := by
      intro n
      induction n with
      | zero =>
        simp [pow_zero]
        <;> simp [Complex.ext_iff, Real.sin_zero, Real.cos_zero]
        <;> norm_num
        <;> try tauto
      | succ n ih =>
        have eq2 : (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) ^ (n + 1) =
            (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) ^ n * (Real.cos (Real.pi / 14) + I * Real.sin (Real.pi / 14)) := by
          ring
        rw [eq2]
        rw [ih]
        simp [Complex.ext_iff, Real.cos_add, Real.sin_add, mul_add, add_mul, mul_comm, mul_assoc]
        <;> ring_nf
        <;> simp [Real.sin_sq, Real.cos_sq]
        <;> ring_nf
        <;> norm_num
        <;> field_simp
        <;> ring_nf
        <;> try linarith
    specialize h1 14
    simpa using h1
  rw [h3]
  have h3' : 14 * (Real.pi / 14) = Real.pi := by
    ring_nf
  rw [h3']
  have eq2 : Real.cos (Real.pi) = -1 := Real.cos_pi
  have eq3 : Real.sin (Real.pi) = 0 := Real.sin_pi
  rw [eq2, eq3]
  all_goals ring_nf <;> simp [Complex.ext_iff]
  <;> try linarith <;> try ring_nf
  all_goals try simp [Complex.ext_iff, Real.sin_pos, Real.sin_sq, Real.cos_sq]
  <;> try ring_nf
  all_goals try simp [Complex.ext_iff, mul_add, mul_add, mul_assoc, Complex.I_sq, mul_add, mul_assoc]
  <;> try ring_nf
  <;> try linarith
  all_goals try simp [Complex.ext_iff, mul_add, mul_add, mul_assoc, Complex.I_sq, Real.sin_sq]
  <;> try ring_nf
  <;> try linarith
  <;> try tauto
  all_goals try simp [Complex.ext_iff, mul_add, mul_add, mul_assoc, Complex.I_sq, mul_add, mul_assoc, Real.sin_sq, Real.cos_sq]
  <;> try norm_num
  all_goals try tauto
  <;> try norm_num