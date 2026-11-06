import Mathlib

open Polynomial


lemma cubic_factor {a b c : ℝ} {u v w : ℝ}
    (hroots : (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {u, v, w}) :
    X ^ 3 + C a * X ^ 2 + C b * X + C c = (X - C u) * (X - C v) * (X - C w) := by
  let p : ℝ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c
  have h1 : p.natDegree = 3 := by
    dsimp only [p]
    compute_degree <;> norm_num
  have h2 : Multiset.card p.roots = p.natDegree := by
    simp [hroots, h1]
  convert (C_leadingCoeff_mul_prod_multiset_X_sub_C h2).symm using 1
  rw [leadingCoeff, h1]
  simpa [p, hroots] using by ring


lemma cubic_vieta
    {a b c : ℝ} (u v w : ℝ)
    (hroots : (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {u, v, w}) :
      a = -(u + v + w) ∧
      b = (u * v + v * w + w * u) ∧
      c = -(u * v * w) := by

  have h_expand : (X - C u) * (X - C v) * (X - C w) = X ^ 3 + C (-(u + v + w)) * X ^ 2 + C (u * v + v * w + w * u) * X + C (-(u * v * w)) := by
    simpa only [C_neg, C_add, C_mul] using by ring

  have h_factor := cubic_factor hroots
  rw [h_expand] at h_factor

  split_ands
  <;> [apply_fun (·.coeff 2) at h_factor;
        apply_fun (·.coeff 1) at h_factor;
        apply_fun (·.coeff 0) at h_factor]
  all_goals
    convert h_factor
    all_goals
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num


theorem useful_lemma_634573
    (a b c : ℝ) (u v w : ℝ) (f : ℝ → ℝ)
    (hf : f = fun (x : ℝ) => x ^ 3 + a * x ^ 2 + b * x + c)
    (h_distinct : u ≠ v ∧ u ≠ w ∧ v ≠ w)
    (hu : f u = 0)
    (hv : f v = 0)
    (hw : f w = 0) :
    a = -(u + v + w) ∧
    b = (u * v + v * w + w * u) ∧
    c = - (u * v * w) := by

  apply cubic_vieta

  -- need to show (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {u, v, w}

  simp only [hf] at hu hv hw

  let p : ℝ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c

  have h_pdegree : p.natDegree = 3 := by simp only [p]; compute_degree!

  have h_pnezero : p ≠ 0 := by
    simp [p]
    refine leadingCoeff_ne_zero.mp ?_
    simp [leadingCoeff, h_pdegree]

  have h_card : p.roots.card ≤ 3 := by
    convert card_roots' p
    simp [h_pdegree]

  refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ h_card)
  refine (Multiset.le_iff_subset ?_).mpr ?_
  . simp
    tauto
  . simp [h_pnezero, p, hu, hv, hw]
