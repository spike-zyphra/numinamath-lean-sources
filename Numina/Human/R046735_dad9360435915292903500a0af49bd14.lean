import Mathlib

open Polynomial Complex

/- Let $a, b, c, d$ be real numbers such that $b-d \geq 5$ and all zeros $x_{1}, x_{2}, x_{3}$, and $x_{4}$ of the polynomial $P(x)=x^{4}+a x^{3}+b x^{2}+c x+d$ are real. Find the smallest value the product $\left(x_{1}^{2}+1\right)\left(x_{2}^{2}+1\right)\left(x_{3}^{2}+1\right)\left(x_{4}^{2}+1\right)$ can take. -/
theorem algebra_248758 :
    IsLeast {(x₁ ^ 2 + 1) * (x₂ ^ 2 + 1) * (x₃ ^ 2 + 1) * (x₄ ^ 2 + 1) | (x₁ : ℝ) (x₂ : ℝ) (x₃ : ℝ) (x₄ : ℝ) (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (_ : b - d ≥ 5) (_ : (X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d).roots = {x₁, x₂, x₃, x₄})} 16 := by
  constructor
  . -- Set x₁ = x₂ = x₃ = x₄ = 1, a = -4, b = 6, c = -4, d = 1
    use 1, 1, 1, 1, -4, 6, -4, 1
    refine ⟨by norm_num, ?_, by norm_num⟩
    -- Show (X - 1) ^ 4 = X ^ 4 - 4 * X ^ 3 + 6 * X ^ 2 - 4 * X + 1
    convert roots_multiset_prod_X_sub_C ({1, 1, 1, 1} : Multiset ℝ)
    simp
    show X ^ 4 + -(4 * X ^ 3) + 6 * X ^ 2 + -(4 * X) + 1 = (X - 1) * ((X - 1) * ((X - 1) * (X - 1)))
    ring
  . rintro _ ⟨x₁, x₂, x₃, x₄, a, b, c, d, h, k, rfl⟩
    set p := X ^ 4 + C a * X ^ 3 + C b * X ^ 2 + C c * X + C d with hp
    have hp₁ : p.natDegree = 4 := by
      rw [hp]
      compute_degree!
    have hp₂ : p.Monic := by
      rw [Monic.def, ← coeff_natDegree, hp₁, hp]
      simp
    -- Show p = (X - x₁) * (X - x₂) * (X - x₃) * (X - x₄)
    have hp₃ := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp₂ (by simp [k, hp₁])
    -- Take x = I and x = -I in the polynomial equality
    have hp₄ := congrArg (aeval I) hp₃
    simp [aeval, k, Complex.coe_algebraMap, Algebra.ofId_apply] at hp₄
    simp [hp, Algebra.ofId_apply, pow_succ] at hp₄
    have hp₅ := congrArg (aeval (-I)) hp₃
    simp [aeval, k, Complex.coe_algebraMap, Algebra.ofId_apply] at hp₅
    simp [hp, Algebra.ofId_apply, pow_succ] at hp₅
    have H : (x₁ ^ 2 + 1) * (x₂ ^ 2 + 1) * (x₃ ^ 2 + 1) * (x₄ ^ 2 + 1) = (b - d - 1) ^ 2 + (a - c) ^ 2 := by
      -- Cast to ℂ
      apply Complex.ofReal_injective
      push_cast
      -- Show (I - z) * (-I - z) = z ^ 2 + 1
      have lem (z : ℂ) : (I - z) * (-I - z) = z ^ 2 + 1 := by
        ring_nf; simp
      calc (_ : ℂ)
        _ = ((I - x₁) * (-I - x₁)) * ((I - x₂) * (-I - x₂)) * ((I - x₃) * (-I - x₃)) * ((I - x₄) * (-I - x₄)) := by rw [lem x₁, lem x₂, lem x₃, lem x₄]
        _ = ((I - ↑x₁) * ((I - ↑x₂) * ((I - ↑x₃) * (I - ↑x₄)))) * ((-I - ↑x₁) * ((-I - ↑x₂) * ((-I - ↑x₃) * (-I - ↑x₄)))) := by ac_rfl
        _ = (1 + -(↑a * I) + -↑b + ↑c * I + ↑d) * (1 + ↑a * I + -↑b + -(↑c * I) + ↑d) := by rw [hp₄, hp₅]
        _ = (b - d - 1) ^ 2 + (a - c) ^ 2 := by ring_nf; simp; ring
    rw [H]
    -- Simple quadratic inequality
    nlinarith
