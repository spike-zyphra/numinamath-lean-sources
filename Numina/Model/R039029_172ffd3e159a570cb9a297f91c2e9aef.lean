import Mathlib

open Polynomial

theorem algebra_10570 {a c : ℝ} (ha : a ≠ 0)
  (h : (C a * X^2 + C 20 * X + C c).roots = {x1, x1})
  (h1 : a + c = 29) (h2 : a < c) : (a, c) = (4, 25) := by

  have hquadratic_factor {a b c x1 x2 : ℝ} (h1 : a ≠ 0) (h2 : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) := by
    letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
    have hp_natDegree_eq_two : p.natDegree = 2 := by
      apply le_antisymm
      . exact natDegree_quadratic_le
      convert Polynomial.card_roots' p
      rw [h2, Multiset.card_pair]
    have hp_natDegree_eq_roots_card : Multiset.card p.roots = p.natDegree := by
      rw [h2, Multiset.card_pair, hp_natDegree_eq_two]
    haveI := C_leadingCoeff_mul_prod_multiset_X_sub_C hp_natDegree_eq_roots_card
    convert this.symm using 1
    rw [leadingCoeff, hp_natDegree_eq_two]
    simpa [p, h2] using by ac_rfl

  have hquadratic_vieta {a b c x1 x2 : ℝ} (h1 : a ≠ 0) (h2 : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    -a * (x1 + x2) = b ∧ a * x1 * x2 = c := by
    letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
    have hp_factor := hquadratic_factor h1 h2
    have hp_expand : C a * (X - C x1) * (X - C x2) = C a * X ^ 2 + C (-a * (x1 + x2)) * X + C (a * x1 * x2) := by
      simp only [C_neg, C_add, C_mul]
      ring
    constructor
    . apply_fun (·.coeff 1) at hp_factor
      convert hp_factor.symm
      simp [hp_expand]
      simp
    apply_fun (·.coeff 0) at hp_factor
    convert hp_factor.symm
    simp [hp_expand]
    simp

  have hvieta := hquadratic_vieta ha h

  simp [show (C a * X^2 + C 20 * X + C c).natDegree = 2 by
    apply le_antisymm
    . exact natDegree_quadratic_le
    convert Polynomial.card_roots' (C a * X ^ 2 + C 20 * X + C c)
    rw [h, Multiset.card_pair]
  ] at hvieta

  -- Now with `h1 : a + c = 29` and `h2 : a < c`
  have h3 : a + c = 29 := h1
  have h4 : -a * (x1 + x1) = (20 : ℝ) := by
    have h5 := (hvieta).1
    nlinarith
  have h5 : a * x1 = -10 := by
    nlinarith
  have h7 : a * x1 ^ 2 = c := by
    have h8 := (hvieta).2
    ring_nf at h8 ⊢
    nlinarith

  -- Now with the fact that `h1 : a + c = 29`
  have h9 : c = 29 - a := by linarith

  -- Substitute `c = 29 - a` into `h7`
  rw [show c = 29 - a by linarith] at h7

  -- Solving the quadratic system
  have h13 : x1 = -10 / a := by
    have h8 : a ≠ 0 := ha
    field_simp
    nlinarith

  rw [h13] at h7
  have h17 : a * ((-10 / a) ^ 2) = 29 - a := by
    linarith

  have h21 : 100 = a * (29 - a) := by
    have h17' : a * ((-10 / a) ^ 2) = 29 - a := by
      linarith
    have h18 : a * ((-10 / a) ^ 2) = 100 / a := by
      field_simp [ha]
      <;> nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption)]
    rw [h18] at h17'
    have h22 : a ≠ 0 := ha
    field_simp at h17'
    nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by assumption)]

  have h31 : a ^ 2 - 29 * a + 100 = 0 := by
    nlinarith

  have h28 : (a - 4) * (a - 25) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h28) with h29 h30
  · -- a - 4 = 0
    have ha4 : a = 4 := by linarith
    have hc25 : c = 25 := by
      linarith
    simp [ha4, hc25]
  · -- a - 25 = 0
    have ha25 : a = 25 := by
      linarith
    have hc4 : c = 4 := by
      linarith
    linarith