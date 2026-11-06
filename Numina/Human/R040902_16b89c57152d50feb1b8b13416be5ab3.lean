import Mathlib

/- If $\sqrt{2\sqrt{t-2}} = \sqrt[4]{7 - t}$, then find $t$. -/
open Real in
theorem algebra_13576 : {t : ℝ | t - 2 ≥ 0 ∧ 7 - t ≥ 0 ∧ √(2 * √(t - 2)) = (7 - t) ^ ((1 : ℝ) / 4)} = {3} := by
  calc
    -- We raise both sides to the fourth power, which is equivalent to squaring twice, in order to get rid of the radicals. The left-hand side becomes $$\left(\sqrt{2\sqrt{t-2}}\right)^4 = \left(2\sqrt{t-2}\right)^2 = 4 \cdot (t-2) = 4t-8.$$The right-hand side becomes $\left(\sqrt[4]{7-t}\right)^4 = 7-t$.
    _ = {t : ℝ | t - 2 ≥ 0 ∧ 7 - t ≥ 0 ∧ 4 * t - 8 = 7 - t} := by
      congr! 2 with t
      apply and_congr_right
      intro ht1
      apply and_congr_right
      intro ht2
      rw [← sq_eq_sq₀ (by positivity) (by positivity), sq_sqrt (by positivity)]
      rw [← sq_eq_sq₀ (by positivity) (by positivity), mul_pow, sq_sqrt (by positivity)]
      norm_num
      rw [← rpow_two, ← rpow_two, ← rpow_mul (by positivity), ← rpow_mul (by positivity), mul_sub]
      norm_num
    -- Setting them equal, $$4t-8 = 7-t \quad\Longrightarrow\quad 5t = 15,$$and $t = \boxed{3}$. Checking, we find that this value does indeed satisfy the original equation.
    _ = _ := by
      ext t
      simp
      constructor
      · rintro ⟨ht1, ht2, ht3⟩
        linarith
      · rintro rfl
        norm_num
