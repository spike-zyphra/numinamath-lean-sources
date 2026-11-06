import Mathlib

open Polynomial

/- Example 10 Determine all polynomials $f(x)$ that satisfy the following condition:

$$

f(x+1)=\frac{1}{2} f[f(x)]+\frac{3}{2} .

$$
 -/
theorem algebra_250301 {f : Polynomial ℝ} (hf : ∀ x, f.eval (x + 1) = (1 / 2) * f.eval (f.eval x) + 3 / 2) :
    f = 3 ∨ f = 2 * X + 1
  := by
    -- We rewrite the equality as an equality of polynomials
    convert_to ∀ x, (f.comp (X + C (1 : ℝ))).eval x = (C (1 / 2) * (f.comp f) + C (3 / 2)).eval x using 0 at hf
    · simp only [one_div, map_one, eval_comp, eval_add, eval_X, eval_one, eval_mul, eval_C]
    replace hf := Polynomial.funext hf

    -- Examine the degree of the left hand side and right hand side
    have degrees := hf
    apply_fun Polynomial.natDegree at degrees

    -- Then f.natDegree = f.natDegree * f.natDegree
    have yep : (1 / 2) ≠ (0 : ℝ)
    · linarith
    simp only [natDegree_add_C, Polynomial.natDegree_C_mul yep, Polynomial.natDegree_comp,
      Polynomial.natDegree_X, mul_one] at degrees

    -- So we have that f.natDegree = 1 or f.natDegree = 0
    cases' mul_left_eq_self₀.mp degrees.symm with h1 h2
    -- We examine equalities of coefficients
    · obtain ⟨a₀, ne_zero_a₀, a₁, h⟩ := Polynomial.natDegree_eq_one.mp h1
      simp only [←h, map_one, add_comp, mul_comp, C_comp, X_comp, one_div] at hf
      ring_nf at hf

      -- We see that a₀ = 2
      have hf' := hf
      apply_fun (fun x => Polynomial.coeff x 1) at hf'
      simp only [coeff_add, coeff_C_succ, coeff_mul_X, coeff_C_zero, zero_add, add_zero, one_div,
        coeff_mul_C, zero_mul] at hf'
      simp only [pow_two (C a₀), mul_coeff_zero, coeff_C_zero] at hf'
      field_simp [ne_zero_a₀] at hf'
      subst hf'

      -- Then we have that a₁ = 1
      apply_fun (fun x => Polynomial.coeff x 0) at hf
      simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, mul_zero, add_zero,
        one_div, zero_mul] at hf
      have eq_one : a₁ = 1 := by linarith
      exact Or.inr (eq_one ▸ h).symm

    -- When n = 0, we have that a₀ = 3
    · obtain ⟨a₀, bb⟩ := Polynomial.natDegree_eq_zero.mp h2
      rw [←bb, map_one, C_comp, one_div, comp_C, eval_C, ←Polynomial.C_mul,
        ←Polynomial.C_add, Polynomial.C_inj] at hf
      have eq_three : a₀ = 3 := by linarith
      exact Or.inl (eq_three ▸ bb).symm