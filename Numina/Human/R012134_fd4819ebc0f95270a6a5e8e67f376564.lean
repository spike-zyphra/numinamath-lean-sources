import Mathlib

open Real

/- 1. Given a positive real number $x$ satisfies $\lg ^{2015} x<\lg ^{2014} x<\lg ^{2016} x$, then the range of $x$ is -/
theorem algebra_224766 {x : ℝ} (hx : 0 < x) :
    (logb 10 x)^2015 < (logb 10 x)^2014 ∧ (logb 10 x)^2014 < (logb 10 x)^2016 ↔
    x ∈ Set.Ioo 0 (1 / 10) := by
  calc
    -- first add (logb 10 x ≠ 0) to the hypothesis as it'll make some work easier
    _ ↔ (logb 10 x)^2015 < (logb 10 x)^2014 ∧ (logb 10 x)^2014 < (logb 10 x)^2016 ∧ (logb 10 x ≠ 0) := by
      simp
      rintro h1 h2
      norm_num
      simp [show x ≠ 0 by linarith, show x ≠ -1 by linarith]
      -- if x = 1 then inequalities cannot be true
      by_contra h
      rw [h] at h1
      simp at h1
    -- change the first inequality to logb 10 x < 1
    _ ↔ logb 10 x < 1 ∧ (logb 10 x)^2014 < (logb 10 x)^2016 ∧ logb 10 x ≠ 0 := by
      simp [-logb_eq_zero]
      rintro h1 h2
      rw [show logb 10 x ^ 2014 = 1 * (logb 10 x ^ 2014) by ring]
      rw [show logb 10 x ^ 2015 = logb 10 x * (logb 10 x) ^ 2014 by ring]
      exact mul_lt_mul_iff_of_pos_right (by positivity)
    -- change the second inequality to 1 < logb 10 x ^ 2
    _ ↔ logb 10 x < 1 ∧ 1 < (logb 10 x)^2 ∧ logb 10 x ≠ 0 := by
      simp [-logb_eq_zero, -one_lt_sq_iff_one_lt_abs]
      rintro h1 h2
      rw [show logb 10 x ^ 2014 = 1 * (logb 10 x ^ 2014) by ring]
      rw [show logb 10 x ^ 2016 = (logb 10 x)^2 * (logb 10 x) ^ 2014 by ring]
      exact mul_lt_mul_iff_of_pos_right (by positivity)
    -- now we can show this is equivalent to logb 10 x < -1
    _ ↔ logb 10 x < -1 := by
      constructor
      -- proving lhs to rhs, we can prove 1 < |logb 10 x| and -1 ≤ logb 10 x ≤ 1, contradiction
      . rintro ⟨h1, h2, h3⟩
        simp at h2
        apply lt_of_not_le
        rintro h
        have := abs_le.mpr ⟨h, h1.le⟩
        linarith
      -- if log 10 x < -1, then we can prove lhs
      . rintro h
        and_intros
        any_goals linarith
        rw [show (1 : ℝ) = 1^2 by ring, show logb 10 x ^ 2 = (- logb 10 x) ^ 2 by ring]
        rw [sq_lt_sq₀ (by linarith) (by linarith)]
        linarith
    -- now we finally prove target by using logb's inequality condition.
    _ ↔ x ∈ Set.Ioo 0 (1 / 10) := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) hx]
      simp [hx]
      norm_cast
      simp