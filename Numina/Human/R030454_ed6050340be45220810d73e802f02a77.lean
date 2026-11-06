import Mathlib

open Real

/- $\sqrt{x^{2}+x+4}+\sqrt{x^{2}+x+1}=\sqrt{2 x^{2}+2 x+9}$. -/
theorem algebra_177982 (x : ℝ) (hx : x^2 + x + 4 ≥ 0 ∧ x^2 + x + 1 ≥ 0 ∧ 2 * x^2 + 2 * x + 9 ≥ 0) :
     sqrt (x^2 + x + 4) + sqrt (x^2 + x + 1) =
    sqrt (2 * x^2 + 2 * x + 9) ↔ x = 0 ∨ x = -1 := by
    apply Iff.intro
    · intro h
      -- After squaring, we get x ^ 2 + x + 4 + 2 * √(x ^ 2 + x + 4) * √(x ^ 2 + x + 1) + (x ^ 2 + x + 1) = 2 * x ^ 2 + 2 * x + 9
      have h : (sqrt (x^2 + x + 4) + sqrt (x^2 + x + 1))^2 = (sqrt (2 * x^2 + 2 * x + 9))^2 := by simp [h]
      rw [add_sq] at h
      repeat rw[sq_sqrt (by linarith)] at h
      -- or √((x ^ 2 + x + 4) * (x ^ 2 + x + 1)) = 2
      have h : √(x ^ 2 + x + 4) * √(x ^ 2 + x + 1) = 2 := by linarith
      rw [← sqrt_mul (by linarith)] at h
      -- From this, (x ^ 2 + x + 4) * (x ^ 2 + x + 1) = 4,
      apply (sqrt_eq_iff_eq_sq (by nlinarith) (by simp)).1 at h
      -- or x (x + 1) (x ^ 2 + x + 5) = 0.
      have h : x * (x + 1) * (x ^ 2 + x + 5) = 0 := by nlinarith
      rcases mul_eq_zero.1 h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact Or.inl h
        · apply Or.inr
          linarith
      · -- Since the discriminant of x ^ 2 + x + 5 = 0 is negative, the only solutions are x = 0 and x = -1.
        have h : 1 * (x * x) + 1 * x + 5 = 0 := by simp_all only [pow_two, one_mul]
        apply (quadratic_eq_zero_iff_discrim_eq_sq (by simp) x).1 at h
        simp [discrim] at h
        norm_num at h
        have : 0 ≤ (2 * x + 1) ^ 2 := by apply sq_nonneg
        linarith
    · -- x = 0 and x = -1 are indeed solutions of the original equation
      intro h
      rcases h with  h | h
      all_goals
        subst h
        norm_num
        have : sqrt 4 = 2 := by
          apply (sqrt_eq_iff_eq_sq (by simp) (by simp)).2
          norm_num
        have : sqrt 9 = 3 := by
          apply (sqrt_eq_iff_eq_sq (by simp) (by simp)).2
          norm_num
        linarith