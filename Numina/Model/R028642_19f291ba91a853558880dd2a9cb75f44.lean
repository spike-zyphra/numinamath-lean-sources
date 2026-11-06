import Mathlib

theorem algebra_20909 {a b c : ℚ} {p : ℝ → ℝ} (hp : ∀ x, p x = a * x ^ 2 + b * x + c) (h1 : p (Real.sqrt 7) = 22) (h2 : p (Real.sqrt 11) = 30) : p (Real.sqrt 17) = 42 := by

  have beq : b = 0 := by
    rw [hp, Real.sq_sqrt (by norm_num)] at h1
    by_contra bz
    have sqrteq : Real.sqrt 7 = ((22 - a * 7 - c) / b : ℚ) := by
      simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat, Rat.cast_mul]
      field_simp
      linarith
    have sqrtirra : Irrational (Real.sqrt 7) := by
      apply Nat.Prime.irrational_sqrt
      exact Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl
    have sqrtne := Irrational.ne_rat sqrtirra ((22 - a * 7 - c) / b)
    contradiction

  have eq1 : (a : ℝ) * 7 + (c : ℝ) = 22 := by
    rw [hp, beq, Real.sq_sqrt (by norm_num)] at h1
    ring_nf at h1 ⊢
    linarith

  have eq2 : (a : ℝ) * 11 + (c : ℝ) = 30 := by
    rw [hp, beq, Real.sq_sqrt (by norm_num)] at h2
    ring_nf at h2 ⊢
    linarith

  have ha : (a : ℝ) = 2 := by
    linarith

  have hc : (c : ℝ) = 8 := by
    linarith

  have h3 : p (Real.sqrt 17) = a * (Real.sqrt 17) ^ 2 + b * (Real.sqrt 17) + c := hp (Real.sqrt 17)

  rw [h3]

  rw [Real.sq_sqrt (by norm_num)]
  rw [show (b : ℝ) = (0 : ℝ) by exact_mod_cast beq]
  rw [show (a : ℝ) = (2 : ℝ) by exact_mod_cast ha]
  rw [show (c : ℝ) = (8 : ℝ) by exact_mod_cast hc]
  all_goals
    norm_num