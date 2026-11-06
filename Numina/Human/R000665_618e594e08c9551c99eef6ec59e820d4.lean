import Mathlib

open Polynomial

/- The quadratic $x^2 + 5x + c$ has roots in the form of $x = \frac{-5 \pm \sqrt{c}}{2}$. What is the value of $c$?-/
theorem algebra_13766 (c : ℝ) (hc : 0 ≤ c) (hroots : (C 1 * X ^ 2 + C 5 * X + C c).roots =
    {(- 5 + √c) / 2, (- 5 - √c) / 2}) : c = 5 := by
  -- We need Vieta's formula here.
  -- Factor quadratic polynomial.
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
  -- Vieta's formula
  have hquadratic_vieta {a b c x1 x2 : ℝ} (hroots : (C a * X ^ 2 + C b * X + C c).roots = {x1, x2}) :
    -a * (x1 + x2) = b ∧ a * x1 * x2 = c := by
    letI p : ℝ[X] := C a * X ^ 2 + C b * X + C c
    have hp_factor := hquadratic_factor hroots
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
    simp
    simp
  -- Using Vieta's formula, we have $(-5+√c)/2(-5-√c)/2=c$.
  specialize hquadratic_vieta hroots
  rcases hquadratic_vieta with ⟨_, hmul⟩
  field_simp at hmul
  ring_nf at hmul
  -- Simplifies to $25 - c = 4c$.
  rw [Real.sq_sqrt hc] at hmul
  -- Hence, we have $c=5$.
  linarith
