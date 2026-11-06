import Mathlib
open Real
/- 5. (7 points) Solve the equation $(\sin x)^{2018}+(\cos x)^{2018}=1$. -/
theorem algebra_137434 (x : ℝ) : (sin x) ^ 2018 + (cos x) ^ 2018 = 1 ↔ ∃ n : ℤ, x = n * π / 2:= by
  constructor
  -- Forward direction: proving that if (sin x)^2018 + (cos x)^2018 = 1, then x = nπ/2 for some integer n
  .
    intro h
    -- Using the fundamental identity sin²x + cos²x = 1
    have h1 : sin x ^ 2 + cos x ^ 2 = 1:= by exact sin_sq_add_cos_sq x
    rw [←h1] at h
    -- Rearranging the equation to show that sin²x(1-sin^2016 x) + cos²x(1-cos^2016 x) = 0
    replace h : sin x ^ 2 * (1 - sin x ^ 2016) + cos x ^ 2 * (1 - cos x ^ 2016) = 0:= by
      ring_nf
      linarith
    -- Establishing basic bounds for sin²x and cos²x
    have g1 : sin x ^ 2 ≥ 0:= by positivity
    have g2 : cos x ^ 2 ≥ 0:= by positivity
    have g3 : sin x ^ 2 ≤ 1:= by linarith
    have g4 : cos x ^ 2 ≤ 1:= by linarith
    -- Rewriting powers to simplify the expressions
    rw [show sin x ^ 2016 = (sin x ^ 2) ^ 1008 by ring_nf] at h
    rw [show cos x ^ 2016 = (cos x ^ 2) ^ 1008 by ring_nf] at h
    -- Proving that powers of sin²x and cos²x are also bounded by 1
    replace g3 : (sin x ^ 2) ^ 1008 ≤ 1:= by exact pow_le_one₀ g1 g3
    replace g4 : (cos x ^ 2) ^ 1008 ≤ 1:= by exact pow_le_one₀ g2 g4
    -- Showing that 1 minus these powers is non-negative
    replace g3 : 1 - (sin x ^ 2) ^ 1008 ≥ 0:= by linarith
    replace g4 : 1 - (cos x ^ 2) ^ 1008 ≥ 0:= by linarith
    -- Proving that the products are non-negative
    replace g3 : sin x ^ 2 * (1 - (sin x ^ 2) ^ 1008) ≥ 0:= by exact mul_nonneg g1 g3
    replace g4 : cos x ^ 2 * (1 - (cos x ^ 2) ^ 1008) ≥ 0:= by exact mul_nonneg g2 g4
    -- Since their sum is 0 and both are non-negative, both must be 0
    replace g3 : sin x ^ 2 * (1 - (sin x ^ 2) ^ 1008) = 0:= by linarith
    replace g4 : cos x ^ 2 * (1 - (cos x ^ 2) ^ 1008) = 0:= by linarith
    simp at g3
    -- Case analysis: either sin²x = 0 or sin²x = 1
    rcases g3 with g3 | g3
    -- Case 1: sin²x = 0, which means sin x = 0
    .
      apply Real.sin_eq_zero_iff.1 at g3
      rcases g3 with ⟨n, rfl⟩
      use 2 * n
      simp
      linarith
    -- Case 2: sin²x = 1, which means cos²x = 0 (from sin²x + cos²x = 1)
    .
      replace g3 : sin x ^ 2 = 1:= by
        by_contra H
        replace H : sin x ^ 2 < 1:= by
          by_contra H1
          push_neg at H1
          replace H1 : sin x ^ 2 = 1:= by linarith
          trivial
        replace H : (sin x ^ 2) ^ 1008 < 1:= by refine pow_lt_one₀ g1 H (by norm_num)
        linarith
      replace h1 : cos x ^ 2 = 0:= by linarith
      simp at h1
      apply Real.cos_eq_zero_iff.1 at h1
      rcases h1 with ⟨n, rfl⟩
      use 2 * n + 1
      simp
  -- Reverse direction: proving that if x = nπ/2 for some integer n, then (sin x)^2018 + (cos x)^2018 = 1
  .
    rintro ⟨n, rfl⟩
    -- Case analysis based on whether n is even or odd
    by_cases hn : Even n
    -- Case 1: n is even, so n = 2k for some integer k
    .
      simp [Even] at hn
      rcases hn with ⟨k, rfl⟩
      ring_nf
      simp
      rw [show ↑k * 2 * π * 2⁻¹ = ↑k * π by ring_nf]
      rw [show sin (k * π) ^ 2018 = (sin (k * π) ^ 2) ^ 1009 by ring_nf]
      rw [show cos (k * π) ^ 2018 = (cos (k * π) ^ 2) ^ 1009 by ring_nf]
      -- When n is even, sin(kπ) = 0 and cos(kπ) = ±1
      have g1 : sin (k * π) = 0:= by exact sin_int_mul_pi k
      have g2:= sin_sq_add_cos_sq (k * π)
      rw [g1] at g2
      ring_nf at g2
      rw [g1, g2]
      simp
    -- Case 2: n is odd, so n = 2k+1 for some integer k
    .
      simp at hn
      simp [Odd] at hn
      rcases hn with ⟨k, rfl⟩
      simp
      -- When n is odd, cos((2k+1)π/2) = 0 and sin((2k+1)π/2) = ±1
      have g1 : cos ((2 * ↑k + 1) * π / 2) = 0:= by
        apply Real.cos_eq_zero_iff.2
        use k
      have g2:= sin_sq_add_cos_sq ((2 * ↑k + 1) * π / 2)
      rw [g1] at g2
      replace g2 : sin ((2 * ↑k + 1) * π / 2) ^ 2 = 1:= by linarith
      rw [show sin ((2 * ↑k + 1) * π / 2) ^ 2018 = (sin ((2 * ↑k + 1) * π / 2) ^ 2) ^ 1009 by ring_nf]
      rw [show cos ((2 * ↑k + 1) * π / 2) ^ 2018 = (cos ((2 * ↑k + 1) * π / 2) ^ 2) ^ 1009 by ring_nf]
      rw [g2, g1]
      simp
