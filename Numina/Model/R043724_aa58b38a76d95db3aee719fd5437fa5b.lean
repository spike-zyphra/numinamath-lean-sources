import Mathlib

open Polynomial

theorem calculus_22737 (p : ℤ[X]) (hp : p = C 8 * X ^ 3 - C 6 * X - C 1) : p.natDegree = 3 ∧ (aeval (Real.cos (20 * Real.pi / 180))) p = 0 ∧ 0 < p.coeff 3 ∧ Finset.gcd {(p.coeff 3), (p.coeff 2), (p.coeff 1), (p.coeff 0)} id = 1 := by
  constructor
  · -- Let's prove that p has degree 3.
    rw [hp]
    compute_degree <;> try norm_num
  constructor
  · -- Let's prove that cos(20°) is a root of p.
    rw [hp]
    simp [Polynomial.aeval, Polynomial.eval]
    have h1 : Real.cos (3 * (20 * Real.pi / 180)) = 4 * Real.cos (20 * Real.pi / 180) ^ 3 - 3 * Real.cos (20 * Real.pi / 180) := by
      rw [Real.cos_three_mul]
    have h2 : 3 * (20 * Real.pi / 180) = Real.pi / 3 := by
      ring_nf
    have h3 : Real.cos (3 * (20 * Real.pi / 180)) = 1 / 2 := by
      rw [h2]
      have h4 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      linarith
    rw [h1] at h3
    have h5 : 8 * Real.cos (20 * Real.pi / 180) ^ 3 - 6 * Real.cos (20 * Real.pi / 180) - 1 = 0 := by
      nlinarith
    norm_num at h5 ⊢
    nlinarith
  constructor
  · -- Show that the leading coefficient is positive
    rw [hp]
    norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt, add_assoc]
  · -- Show that the coefficients are coprime
    rw [hp]
    norm_num [Polynomial.coeff_eq_zero_of_natDegree_lt, add_assoc]
    all_goals try native_decide