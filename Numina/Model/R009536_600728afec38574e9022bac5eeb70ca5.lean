import Mathlib
open Polynomial

theorem algebra_13919 {p q r : ℝ} (h : (X^3 - 9 * X^2 + 8 * X + 2 : ℝ[X]).roots = [p, q, r]) : 1 / p^2 + 1 / q^2 + 1 / r^2 = 25 := by
  let f : ℝ[X] := X^3 - 9 * X^2 + 8 * X + 2
  have f0 : f.coeff 0 = 2 := by simp [f]
  have f1 : f.coeff 1 = 8 := by simp [f]
  have f2 : f.coeff 2 = -9 := by simp [f, Polynomial.coeff_X_of_ne_one]
  have f3 : f.coeff 3 = 1 := by simp [f, Polynomial.coeff_X_of_ne_one]
  have f4 : f.natDegree = 3 := by
    simp [f]
    have : (X ^ 3 - 9 * X ^ 2 + 8 * X + 2 : ℝ[X]) = (C 1 * X ^ 3 + C (-9) * X ^ 2 + C 8 * X + C 2) := by
      simp
      have k1 : (9 : ℝ[X]) = C 9 := by
        rw [show (9 : ℝ) = (9 : ℕ) by simp, C_eq_natCast]
        simp
      have k2 : (8 : ℝ[X]) = C 8 := by
        rw [show (8 : ℝ) = (8 : ℕ) by simp, C_eq_natCast]
        simp
      have k3 : (2 : ℝ[X]) = C 2 := by
        rw [show (2 : ℝ) = (2 : ℕ) by simp, C_eq_natCast]
        simp
      rw [k1, k2, k3]
      ring
    rw [this]
    exact natDegree_cubic (by norm_num)
  have f5 : f.leadingCoeff = 1 := by
    rw [← Polynomial.coeff_natDegree, f4, f3]
  have f6 : f ≠ 0 := by
    intro hf
    rw [hf] at f0
    simp at f0

  have hroots {x} (hx : x ∈ ([p, q, r] : Multiset ℝ)) : x ≠ 0 := by
    have k := mem_roots_iff_aeval_eq_zero (x  := x) f6
    rw [← h] at hx
    simp [hx, f] at k
    rintro rfl
    simp at k

  have hp : p ≠ 0 := hroots (by simp)
  have hq : q ≠ 0 := hroots (by simp)
  have hr : r ≠ 0 := hroots (by simp)

  have ⟨h1, h2, h3⟩ : p + q + r = 9 ∧ p * q + q * r + r * p = 8 ∧ p * q * r = -2 := by
    have H1 := coeff_eq_esymm_roots_of_card (p := f)
    simp [h, f4] at H1
    refine ⟨?_, ?_, ?_⟩
    . specialize H1 (show 2 ≤ 3 by simp)
      simp [f2, f5, Multiset.esymm, Multiset.powersetCard] at H1
      linarith only [H1]
    . specialize H1 (show 1 ≤ 3 by simp)
      simp [f1, f5, Multiset.esymm, Multiset.powersetCard] at H1
      linarith only [H1]
    . specialize H1 (show 0 ≤ 3 by simp)
      simp [f0, f5, Multiset.esymm, Multiset.powersetCard] at H1
      linarith only [H1]

  have h4 : 1 / p^2 + 1 / q^2 + 1 / r^2 = ( (q * r)^2 + (p * r)^2 + (p * q)^2 ) / ( (p * q * r)^2 ) := by
    field_simp [hp, hq, hr]
    ring_nf

  have h5 : (q * r)^2 + (p * r)^2 + (p * q)^2 = 100 := by
    nlinarith [h1, h2, h3]

  have h6 : (p * q * r)^2 = 4 := by
    nlinarith [h3]

  rw [h4]
  rw [h5, h6]
  norm_num