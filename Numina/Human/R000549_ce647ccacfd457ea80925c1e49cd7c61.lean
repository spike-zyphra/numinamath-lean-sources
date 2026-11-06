import Mathlib

open Polynomial

/- Let $d$ and $e$ denote the solutions of $3x^2+10x-25=0$. Find $(d-e)^2$.-/
theorem algebra_12294 {d e : ℝ} (hroots : (C (3 : ℝ) * X ^ 2 + C (10 : ℝ) * X + C (-25 : ℝ)).roots = ({d, e} : Multiset ℝ)) :
    (d - e) ^ 2 = 400 / 9 := by
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
  -- Notice that $(d-e)^2=(d+e)^2-4de$.
  rw [show (d - e) ^ 2 = (d + e) ^ 2 - 4 * d * e by ring]
  field_simp
  -- Using Vieta's formula, we have $d+e=-10/3$ and $de=-25/3$.
  specialize hquadratic_vieta hroots
  rcases hquadratic_vieta with ⟨hdemul, hdeadd⟩
  apply_fun (· ^ 2) at hdemul
  -- Hence $(d-e)^2=400/9$.
  linear_combination hdemul - 12 * hdeadd
