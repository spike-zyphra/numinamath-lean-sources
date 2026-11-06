import Mathlib

open Polynomial
/-
The polynomial $f(x)$ satisfies $f(x + 1) - f(x) = 6x + 4.$  Find the leading coefficient of $f(x).$
-/
theorem algebra_4315 {f : Polynomial ℝ} (hf : f.comp (X + C 1) - f = 6 * X + C 4) : leadingCoeff f = 3 := by
  -- Looking at the given equation, $f(x + 1) - f(x)$ equals $6x + 4$. That means the original $f(x)$ must be a quadratic polynomial because the degree is one higher. So that $f(x)$ can be written as : $f(x) = ax^2 + bx + c$.
  have h1 : ∃ a b c, a ≠ 0 ∧ f = C a * X ^ 2 + C b * X + C c := by
    have hf' : f.natDegree ≥ 2 := by
      by_contra! h
      simp [Nat.lt_iff_add_one_le] at h
      apply Polynomial.eq_X_add_C_of_natDegree_le_one at h
      rw [h] at hf
      simp [mul_add] at hf
      suffices (6 : ℝ) = 0 by linarith
      rw [show (6 : ℝ) = (6 * (X : ℝ[X]) + C 4).coeff 1 by simp, ← hf]
      simp
    -- The degree of $f(x)$ is one higher than the degree of $f(x+1) - f(x)$.
    have h11 : (f.comp (X + C 1) - f).natDegree = f.natDegree - 1 := by
      have g1 : (f.comp (X + C 1) - f).natDegree ≤ f.natDegree := by
        have := Polynomial.natDegree_comp_le (p := f) (q := X + C 1)
        simp at this
        rw [show (1 : ℝ[X]) = C 1 by simp, Polynomial.natDegree_X_add_C, mul_one] at this
        rw [show f.natDegree = max ((f.comp (X + C 1)).natDegree) (f.natDegree) by omega]
        apply Polynomial.natDegree_sub_le
      -- The coefficient of $f(x+1) - f(x)$ of degree (deg(f) - 1) is not equal to zero.
      have g2 : (f.comp (X + C 1) - f).coeff (f.natDegree - 1) ≠ 0 := by
        suffices (f.comp (X + C 1) - f).coeff (f.natDegree - 1) = f.natDegree * (f.coeff f.natDegree) by
          rw [this]
          apply mul_ne_zero (by norm_cast; omega)
          rw [Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
          by_contra! h
          suffices f.natDegree = 0 by omega
          simp [h]
        nth_rw 1 [Polynomial.as_sum_range_C_mul_X_pow f]
        simp [add_pow]
        simp [Finset.sum_range_succ]
        have ineq1 : f.natDegree - 1 < f.natDegree + 1 := by omega
        simp [ineq1, ← sub_add_eq_add_sub]
        rw [Nat.choose_symm (by omega), Nat.choose_one_right]
        nth_rw 1 [show f.natDegree = f.natDegree - 1 + 1 by omega, Finset.sum_range_succ]
        simp [mul_comm]
        apply Finset.sum_eq_zero
        intro x hx
        simp at hx
        simp [hx]
        intro hx'
        right
        exact Nat.choose_eq_zero_of_lt hx
      -- The coefficient of $f(x+1) - f(x)$ of degree deg(f) is equal to zero.
      have g3 : (f.comp (X + C 1) - f).coeff f.natDegree = 0 := by
        nth_rw 1 [Polynomial.as_sum_range_C_mul_X_pow f]
        simp [add_pow]
        simp [Finset.sum_range_succ]
        apply Finset.sum_eq_zero
        intro x hx
        simp at hx
        simp [hx]
        intro hx'
        right
        exact Nat.choose_eq_zero_of_lt hx
      suffices (f.comp (X + C 1) - f).natDegree ≥ (f.natDegree - 1) by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at g1
        suffices (f.comp (X + C 1) - f).natDegree < f.natDegree by omega
        rw [Polynomial.natDegree_lt_iff_degree_lt, Polynomial.degree_lt_iff_coeff_zero]
        intro n hn
        rw [le_iff_eq_or_lt] at hn
        rcases hn with (rfl | hn)
        · exact g3
        · exact g1 n hn
        rw [hf]
        by_contra! h
        suffices (6 : ℝ) = 0 by aesop
        rw [show (6 : ℝ) = (6 * (X : ℝ[X]) + C 4).coeff 1 by simp, h]
        simp
      exact Polynomial.le_natDegree_of_ne_zero g2
    rw [hf] at h11
    simp at h11
    have : f.natDegree = 2 := by omega
    use leadingCoeff f, f.coeff 1, f.coeff 0
    simp
    constructor
    · by_contra h
      rw [h] at hf
      simp at hf
      suffices (6 : ℝ) = 0 by aesop
      rw [show (6 : ℝ) = (6 * (X : ℝ[X]) + C 4).coeff 1 by simp, ← hf]
      simp
    · nth_rw 1 [Polynomial.as_sum_range_C_mul_X_pow f]
      simp [this]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [← Polynomial.coeff_natDegree, this]
      ring
  obtain ⟨a, b, c, ha, hf'⟩ := h1
  -- let's compute $f(x + 1) - f(x): f(x + 1) - f(x) = ax^2 + (2a + b)x + (a + b + c) - ax^2 + bx + c = 2ax+(a+b) = 6x + 4$.
  have h2 : 2 * C a * X + C (a + b) = 6 * X + 4 := by
    rw [hf'] at hf
    simp at hf
    ring_nf at hf
    rw [C_add]
    ring_nf
    rw [hf, add_comm]
    congr
  rw [hf', Polynomial.leadingCoeff_quadratic ha]
  -- Coefficient of x: 2a = 6
  have h4 : (6 * X + 4).coeff 1 = 2 * a := by
    simp [← h2]
  simp at h4
  linarith