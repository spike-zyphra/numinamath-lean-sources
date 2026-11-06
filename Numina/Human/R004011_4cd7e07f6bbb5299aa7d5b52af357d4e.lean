import Mathlib

open Complex

/- The Bolognese Bombelli Ráfael was the first to elaborate on the cube root of a complex number in his algebra, which appeared in Italian in 1579. He indeed writes that:


$$

2+\sqrt{-121} \text{ has the cube root } 2+\sqrt{-1}

$$


Considering that from an algebraic perspective, $\sqrt[3]{a}$ is nothing but the solution to the equation $x^{3}=a$, it is required: a) to prove that $2+\sqrt{-1}$ is indeed the cube root of $2+\sqrt{-121}$; b) and to determine the other two values of $\sqrt[3]{2+\sqrt{-121}}$. -/

-- lemma for I^3 = -I
lemma l_I_pow_three : I^3 = -I := by
  rw [pow_succ]
  simp

-- lemma for I^5 = I
lemma l_I_pow_five : I^5 = I := by
  rw [pow_succ, pow_succ, l_I_pow_three]
  simp

theorem algebra_230093 {x : ℂ} : x^3 = 2 + √121 * I ↔
    x = 2 + I ∨ x = 1/2 * (2 + I) * (-1 + √3 * I) ∨ x = -1/2 * (2 + I) * (1 + √3 * I) := by
  -- simplify √121
  rw [show (121 : ℝ) = 11^2 by ring, Real.sqrt_sq (by norm_num)]
  push_cast
  calc
    -- take all terms to lhs
    _ ↔ x^3 - (2 + 11 * I) = 0 := by
      constructor <;> (rintro h; linear_combination h)
    -- factorizae the equation
    _ ↔ (x - (2 + I)) * (x - 1/2 * (2 + I) * (-1 + √3 * I : ℂ)) *
        (x - -1/2 * (2 + I) * (1 + √3 * I : ℂ)) = 0 := by
      ring_nf
      simp
      rw [← ofReal_pow, Real.sq_sqrt (by norm_num), l_I_pow_three, l_I_pow_five]
      push_cast
      ring_nf
    -- product equal 0 means one of the term is 0
    _ ↔ x - (2 + I) = 0 ∨ x - 1/2 * (2 + I) * (-1 + √3 * I : ℂ) = 0 ∨
        x - -1/2 * (2 + I) * (1 + √3 * I : ℂ) = 0 := by
      simp
      tauto
    -- now taking terms to rhs proves goal
    _ = _ := by
      repeat rw [sub_eq_zero]