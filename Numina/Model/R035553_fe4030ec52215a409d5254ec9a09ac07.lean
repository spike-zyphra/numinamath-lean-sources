import Mathlib

theorem calculus_14510 (θ : ℝ) (h : Real.cos θ = 1 / 3) :
    Real.cos (5 * θ) = 241 / 243 := by
  have h3 : Real.cos (5 * θ) = 16 * (Real.cos θ) ^ 5 - 20 * (Real.cos θ) ^ 3 + 5 * (Real.cos θ) := by
    have h4 : Real.cos (5 * θ) = Real.cos (2 * (2 * θ) + θ) := by ring
    rw [h4]
    have h5 : Real.cos (2 * (2 * θ) + θ) = Real.cos (2 * (2 * θ)) * Real.cos θ - Real.sin (2 * (2 * θ)) * Real.sin θ := by
      rw [Real.cos_add]
    have h6 : Real.cos (2 * (2 * θ)) = 2 * (Real.cos (2 * θ)) ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    have h7 : Real.sin (2 * (2 * θ)) = 2 * Real.sin (2 * θ) * Real.cos (2 * θ) := by
      rw [Real.sin_two_mul]
    have h8 : Real.cos (2 * θ) = 2 * (Real.cos θ) ^ 2 - 1 := by
      rw [Real.cos_two_mul]
    have h9 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by
      rw [Real.sin_two_mul]
    -- Use sin^2 θ + cos^2 θ = 1 to express sin θ in terms of cos θ
    -- We know from previous calculation that sin²θ = 8/9, so sin θ = ± 2√2 / 3
    -- But since we are squaring, it will not matter for the final computation
    have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at h1
    have h2 : Real.sin θ ^ 2 = 8 / 9 := by nlinarith
    rw [h5, h6, h7, h8, h9]
    -- Substitute sin θ ^ 2 = 8 / 9
    -- The expression involves powers of cos θ and sin θ, which we can simplify using algebra
    -- But since Lean can handle arithmetic expressions, we can normalize and simplify using Lean's capabilities
    -- Need to express sin θ ^ k and cos θ ^k in terms of cos θ
    -- Since we have ± sqrt(8/9) for sin θ, but squaring would make it (8/9)
    -- After expanding, all terms will result in powers of cos θ
    -- Because the final expression is a polynomial in cos θ, Lean's algebra will handle it correctly
    -- without needing to explicitly substitute sin θ = ± 2√2 / 3
    -- Let's compute the expansion manually to check:
    -- cos 5θ = 2(2cos²θ -1)² -1)cosθ - 2(2sinθcosθ)(2cos²θ -1)(2sinθ)
    -- This seems complicated, alternative expansion
    -- cos 5θ = cos(2θ + 2θ + θ) = cos(4θ + θ)
    -- Using cos(a+b) = cos a cos b - sin a sin b
    -- cos(4θ + θ) = cos 4θ cos θ - sin 4θ sin θ
    -- cos 4θ = 2cos² 2θ -1 = 2(2cos²θ -1)^2 -1
    -- sin 4θ = 2sin 2θ cos 2θ = 2(2sinθcosθ)(2cos²θ -1)
    -- sin² 4θ = 1 - cos² 4θ
    -- We need to handle powers of sin θ and cos θ. The final expression will be a polynomial in cos θ
    -- Let's compute it using Lean's algebra:
    -- We need to substitute sin²θ = 8/9 into all terms
    -- Now expand all terms in Lean with that substitution
    -- The key is that Lean will reduce the expression to a polynomial in cosθ because
    -- all powers of sinθ will be replaced by powers of (8/9) or similar expressions
    -- So after substituting sin²θ = 8/9, all higher powers will be fractions
    -- Let Lean do the algebra.
    -- Note: Lean can also compute coefficients
    -- Let's compute coefficients
    -- We can compute it using Lean's computations
    -- Since we're going to get a polynomial in cosθ, let Lean do it
    -- Expanding of all terms and simplification will lead to the final polynomial form
    -- Let's complete that in Lean
    ring_nf
    <;> simp [pow_two, pow_three, pow_succ, pow_zero, mul_add, add_mul, mul_comm]
    <;> ring_nf
    <;> norm_num [h, h2]
  rw [h3, h]
  norm_num