import Mathlib

/- Let $p(x)$ be quadratic with rational coefficients.  If $p(\sqrt{7}) = 22$ and $p(\sqrt{11}) = 30,$ then find $p(\sqrt{17}).$ -/
theorem algebra_20909 {a b c : ℚ} {p : ℝ → ℝ} (hp : ∀ x, p x = a * x ^ 2 + b * x + c) (h1 : p (Real.sqrt 7) = 22) (h2 : p (Real.sqrt 11) = 30) : p (Real.sqrt 17) = 42 := by
  -- $b = 0$ since $\sqrt{7} is irrational$
  have beq : b = 0 := by
    rw [hp, Real.sq_sqrt (by exact Nat.ofNat_nonneg' 7)] at h1
    by_contra contra
    have sqrteq : Real.sqrt 7 = ((22 - a * 7 - c) / b : ℚ) := by
      simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_mul]
      field_simp
      linarith
    have sqrtirra : Irrational (Real.sqrt 7) := by
      apply Nat.Prime.irrational_sqrt
      exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
    have sqrtne := Irrational.ne_rat sqrtirra ((22 - a * 7 - c) / b)
    contradiction
  -- Solve the equation system, we find $a = 2$ and $c = 8$
  rw [hp, beq, Real.sq_sqrt (by exact Nat.ofNat_nonneg' 7)] at h1
  simp only [Rat.cast_zero, zero_mul, add_zero] at h1
  rw [hp, beq, Real.sq_sqrt (by exact Nat.ofNat_nonneg' 11)] at h2
  simp only [Rat.cast_zero, zero_mul, add_zero] at h2
  have aeq : a = 2 := by
    have aeq : (a : ℝ) = (2 : ℚ) := by
      rw [Rat.cast_ofNat]
      linarith
    exact (Mathlib.Tactic.Rify.ratCast_eq a 2).mpr aeq
  have ceq : c = 8 := by
    have ceq : (c : ℝ) = (8 : ℚ) := by
      rw [Rat.cast_ofNat]
      linarith
    exact (Mathlib.Tactic.Rify.ratCast_eq c 8).mpr ceq
  -- So $p(\sqrt{17}) = 42$
  rw [hp, aeq, beq, ceq, Real.sq_sqrt (by exact Nat.ofNat_nonneg' 17)]
  ring