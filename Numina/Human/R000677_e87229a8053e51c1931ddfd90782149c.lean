import Mathlib

/-Let $a$, $b$, and $c$ be the roots of $x^3 - 20x^2 + 18x - 7 = 0$. Compute \[(a+b)^2 + (b+c)^2 + (c+a)^2.\]-/
theorem algebra_13884 (a b c : ℂ) (hx: ∀x, (x - a) * (x - b) * (x - c) = x^3 - 20*x^2 + 18*x - 7)
    : (a+b)^2+(b+c)^2+(c+a)^2 = 764 := by
  -- expand hx
  have eq₁ : ∀x, -(a + b + c) * x^2 + (a * b + a * c + b * c) * x - (a * b * c) =
             - 20*x^2 + 18*x - 7 := by
    intro x
    specialize hx x
    apply add_left_cancel
    case a => exact x^3
    have : x ^ 3 + (-20 * x ^ 2 + 18 * x - 7) = x^3 - 20*x^2 + 18*x - 7 := by
      apply Complex.ext
      repeat simp; linarith
    rw [this, hx.symm]
    ring_nf
  -- simplify eq₁
  have eq₂ : ∀x, (-(a + b + c) - (-20)) * x^2
           + ((a * b + a * c + b * c) - 18) * x
           + (-(a * b * c) - (-7)) = 0 := by
    intro x
    have : a * b * c = 7 := by
      specialize hx 0
      simp at hx
      exact hx
    rw [this]
    simp
    specialize eq₁ x
    rw [this] at eq₁
    simp at eq₁
    rw [←sub_eq_iff_eq_add'] at eq₁
    rw [sub_mul, add_mul, add_sub, eq₁.symm]
    ring_nf
  simp at eq₂
  have : (a + b + c) = 20 ∧
         (a * b + a * c + b * c) = 18 ∧
         (a * b * c) = 7 := by
    have : ∃(P : Polynomial ℂ),
             P = (Polynomial.C (-(a + b + c) - (-20))) * Polynomial.X^2
               + (Polynomial.C ((a * b + a * c + b * c) - 18)) * Polynomial.X
               + (Polynomial.C (-(a * b * c) - (-7))) := by simp
    rcases this with ⟨P, hP⟩
    have : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      simp
      have : {x | Polynomial.eval x P = 0} = Set.univ := by
        ext x
        simp
        rw [hP]
        simp
        specialize eq₂ x
        exact eq₂
      rw [this]
      exact Set.infinite_univ
    have coeff_0 : P.coeff 0 = (-(a * b * c) - -7) := by
      rw [hP]
      simp
    have coeff_1 : P.coeff 1 = (a * b + a * c + b * c) - 18 := by
      rw [hP]
      simp
      rw [←Polynomial.C_neg, ←Polynomial.C_neg, ←Polynomial.C_neg]
      rw [←Polynomial.C_add, ←Polynomial.C_add, ←Polynomial.C_add]
      rw [Polynomial.coeff_C_mul_X_pow]
      simp
    have coeff_2 : P.coeff 2 = -(a + b + c) - (-20) := by
      rw [hP]
      simp
      rw [←Polynomial.C_neg, ←Polynomial.C_neg, ←Polynomial.C_neg]
      rw [←Polynomial.C_add, ←Polynomial.C_add, ←Polynomial.C_add]
      rw [Polynomial.coeff_C_mul_X_pow]
      simp
    rw [this, Polynomial.coeff_zero, Eq.comm, sub_eq_zero, Eq.comm] at coeff_0 coeff_1 coeff_2
    constructor
    · rw [neg_eq_iff_eq_neg] at coeff_2
      rw [coeff_2]
      simp
    · constructor
      · rw [coeff_1]
      · simp at coeff_0
        exact coeff_0.symm
  -- Expanding, we get \[(a+b)^2+(b+c)^2+(c+a)^2 = 2(a^2+b^2+c^2) + 2(ab+bc+ca).\]To compute this expression, note that \[(a+b+c)^2 = (a^2+b^2+c^2) + 2(ab+bc+ca).\]Then we can write the given expression in terms of $a+b+c$ and $ab+bc+ca$: \[\begin{aligned} 2(a^2+b^2+c^2) + 2(ab+bc+ca) &=[2(a^2+b^2+c^2) + 4(ab+bc+ca)] - 2(ab+bc+ca) \\ &=  2(a+b+c)^2 - 2(ab+bc+ca). \end{aligned}\]By Vieta's formulas, $a+b+c=20$ and $ab+bc+ca=18$, so the answer is $2 \cdot 20^2 - 2 \cdot 18 = \boxed{764}.$
  rw [show (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 = 2 * (a + b + c) ^ 2 - 2 * (a * b + a * c + b * c) by ring_nf, this.1, this.2.1]
  norm_num
