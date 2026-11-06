import Mathlib
open Real

/- Find all $x$ between $-\frac{\pi}{2}$ and $\frac{\pi}{2}$ such that $1-\sin ^{4} x-\cos ^{2} x=\frac{1}{16}$.-/
theorem algebra_610954 :
    {x : ℝ | -π / 2 ≤ x ∧ x ≤ π / 2 ∧ 1 - sin x ^ 4 - cos x ^ 2 = 1 / 16} = {-5 * π / 12, -π / 12, π / 12, 5 * π / 12} := by
  -- Simplify the goal into two parts.
  ext x
  simp [-one_div]
  apply Iff.intro
  . -- First show that if the equation is satisfied for x ∈ [-π / 2, π / 2], then x belongs to the set of four solutions.
    rintro ⟨hx₀, hx₁, h₀⟩
    -- Rewrite the equation as 16(sin x ^ 2) ^ 2 - 16(sin x ^ 2) + 1 = 0, or one step forward, directly as (2 (sin x ^ 2) - 1) ^ 2 = 3 / 4.
    replace h₀ : (2 * sin x ^ 2 - 1) ^ 2 = (sqrt 3 / 2) ^ 2 := by
      rw [div_pow, sq_sqrt (by positivity)]
      -- We only need to use the fact that sin x ^ 2 + cos x ^ 2 = 1.
      linarith only [h₀, cos_sq_add_sin_sq x]
    -- We have the square of (2sin x ^ 2 - 1) and sqrt 3 / 2 equal, so we divide into two cases.
    rw [sq_eq_sq_iff_eq_or_eq_neg] at h₀
    rcases h₀ with (h₀ | h₀)
    . -- We now have cos 2x = 1 - 2 sin x ^ 2 = -√3 / 2 = -cos (π / 6).
      replace h₀ : cos (2 * x) = -cos (π / 6) := by
        rw [cos_pi_div_six]
        -- The fact that cos 2x = 1 - 2 sin x ^ 2 can be derived from cos 2x = cos x ^ 2 - sin x ^ 2 and cos ^ 2 + sin x ^ 2 = 1 combined.
        linarith only [h₀, cos_two_mul' x, cos_sq_add_sin_sq x]
      -- Change -cos (π / 6) to cos (-5π / 6).
      rw [<-cos_pi_sub] at h₀
      -- Since cos 2x = cos (5π / 6), we either have 2x = 5π / 6 or 2x = -5π / 6.
      obtain ⟨k, h₁⟩ := cos_eq_cos_iff.mp h₀
      rcases h₁ with (h₁ | h₁)
      . -- We have 2x + 2kπ = 5π / 6, and we want to show that k = 0 using the assumed range of x, so we have x = 5π / 12.
        simp [show k = 0 by linarith [show k > -1 by rify; nlinarith [pi_pos], show k < 1 by rify; nlinarith [pi_pos]]] at h₁
        iterate 3 right
        linarith only [h₁]
      . -- We have -2x + 2kπ = 5π / 6, and we again want to show that k = 0 using the assumed range of x, so that x = -5π / 12.
        simp [show k = 0 by linarith [show k > -1 by rify; nlinarith [pi_pos], show k < 1 by rify; nlinarith [pi_pos]]] at h₁
        left
        linarith only [h₁]
    . -- We now have cos 2x = 1 - 2 sin x ^ 2 = √3 / 2 = cos (π / 6).
      replace h₀ : cos (2 * x) = cos (π / 6) := by
        rw [cos_pi_div_six]
        -- The fact that cos 2x = 1 - 2 sin x ^ 2 can be derived from cos 2x = cos x ^ 2 - sin x ^ 2 and cos ^ 2 + sin x ^ 2 = 1 combined.
        linarith only [h₀, cos_two_mul' x, cos_sq_add_sin_sq x]
      -- Since cos 2x = cos (π / 6), we either have 2x = π / 6 or 2x = -π / 6.
      obtain ⟨k, h₁⟩ := cos_eq_cos_iff.mp h₀
      rcases h₁ with (h₁ | h₁)
      . -- We have 2x + 2kπ = π / 6, and we want to show that k = 0 using the assumed range of x, so we have x = π / 12.
        simp [show k = 0 by linarith [show k > -1 by rify; nlinarith [pi_pos], show k < 1 by rify; nlinarith [pi_pos]]] at h₁
        iterate 2 right
        left
        linarith only [h₁]
      . -- We have -2x + 2kπ = π / 6, and we again want to show that k = 0 using the assumed range of x, so that x = -π / 12.
        simp [show k = 0 by linarith [show k > -1 by rify; nlinarith [pi_pos], show k < 1 by rify; nlinarith [pi_pos]]] at h₁
        right
        left
        linarith only [h₁]
  . -- We now show that the values -5π / 12, -π / 12, π / 12 and 5π / 12 indeed satisfy the condition.
    rintro (hx | hx | hx | hx)
    all_goals
      refine ⟨by linarith [pi_pos], by linarith [pi_pos], ?_⟩
      -- Rewrite the equation as 16(sin x ^ 2) ^ 2 - 16(sin x ^ 2) + 1 = 0, or one step forward, directly as (2 (sin x ^ 2) - 1) ^ 2 = 3 / 4.
      suffices (2 * sin x ^ 2 - 1) ^ 2 = (sqrt 3 / 2) ^ 2 by
        rw [div_pow, sq_sqrt (by positivity)] at this
        -- We only need to use the fact that sin x ^ 2 + cos x ^ 2 = 1.
        linarith only [this, cos_sq_add_sin_sq x]
      rw [hx]
    -- Simplify the expression for x = -5π / 12, -π / 12, π / 12 and 5π / 12 respectively.
    . rw [neg_div, sin_neg, neg_sq, show 5 * π / 12 = π / 2 - π / 12 by linarith, sin_pi_div_two_sub]
      -- Use double angle formula of cosine, and that cos (π / 6) = sqrt 3 / 2.
      rw [<-cos_two_mul, show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six]
    . rw [neg_div, sin_neg, neg_sq]
      -- Use double angle formula of cosine (the version of sin x ^ 2 = (1 - cos 2x) / 2), and that cos (π / 6) = sqrt 3 / 2.
      rw [sin_sq_eq_half_sub, show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six]
      ring
    . -- Use double angle formula of cosine (the version of sin x ^ 2 = (1 - cos 2x) / 2), and that cos (π / 6) = sqrt 3 / 2.
      rw [sin_sq_eq_half_sub, show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six]
      ring
    . rw [show 5 * π / 12 = π / 2 - π / 12 by linarith, sin_pi_div_two_sub]
      -- Use double angle formula of cosine, and that cos (π / 6) = sqrt 3 / 2.
      rw [<-cos_two_mul, show 2 * (π / 12) = π / 6 by ring, cos_pi_div_six]
