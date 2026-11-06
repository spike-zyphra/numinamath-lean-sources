import Mathlib

open Polynomial

theorem inequalities_205736 {c x y: ℝ}
    (h : (X ^ 2 + (C (-c)) * X + C (- c)).roots = {x, y}) :
    x ^ 3 + y ^ 3 + (x * y) ^ 3 ≥ 0 := by

  have hquadratic_factor {a b c x1 x2 : ℝ} (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
      C a * X ^ 2 + C b * X + C c = C a * (X - C x1) * (X - C x2) := by
    letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
    have hp_natDegree_eq_two : p.natDegree = 2 := by
      apply le_antisymm
      . exact natDegree_quadratic_le
      convert Polynomial.card_roots' p
      rw [hroots, Multiset.card_pair]
    have hp_natDegree_eq_roots_card : Multiset.card p.roots = p.natDegree := by
      rw [hroots, Multiset.card_pair, hp_natDegree_eq_two]
    haveI := C_leadingCoeff_mul_prod_multiset_X_sub_C hp_natDegree_eq_roots_card
    convert this.symm using 1
    rw [leadingCoeff, hp_natDegree_eq_two]
    simpa [p, hroots] using by ac_rfl

  have hquadratic_vieta {a b c x1 x2 : ℝ} (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
      -a * (x1 + x2) = b ∧ a * x1 * x2 = c := by
    letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
    have hp_factor := hquadratic_factor hroots
    have eq1 := congr_arg (fun f => f.eval 0) hp_factor
    simp at eq1
    have eq2 := congr_arg (fun f => f.eval 1) hp_factor
    simp at eq2
    constructor <;> nlinarith

  have h1 := (hquadratic_vieta (show (C 1 * X ^ 2 + (C (-c)) * X + C (-c)).roots = {x, y} by simpa using h))
  have h2 : -1 * (x + y) = -c := by
    norm_num at h1 ⊢
    linarith [h1.1]
  have h3 : 1 * (x * y) = -c := by
    norm_num at h1 ⊢
    linarith [h1.2]

  have h4 : x + y = c := by linarith
  have h5 : x * y = -c := by nlinarith

  have eq1 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) := by
    ring

  have eq2 : x ^ 3 + y ^ 3 = 3 * c ^ 2 + c ^ 3 := by
    rw [eq1, h4, h5]
    nlinarith

  have eq3 : (x * y) ^ 3 = -c ^ 3 := by
    rw [h5]
    ring

  have eq4 : x ^ 3 + y ^ 3 + (x * y) ^ 3 = 3 * c ^ 2 := by
    nlinarith [eq2, eq3]

  have h6 : 3 * c ^ 2 ≥ 0 := by
    have h7 : c ^ 2 ≥ 0 := sq_nonneg c
    linarith

  linarith [eq4, h6]