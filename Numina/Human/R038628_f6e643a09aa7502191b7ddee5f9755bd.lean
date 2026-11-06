import Mathlib

/- If
\[k = \sin^6 \theta + \cos^6 \theta = \sin 2 \theta,\]then find $k.$ -/
theorem calculus_23100 (θ : ℝ) (k : ℝ) (h : k = Real.sin θ ^ 6 + Real.cos θ ^ 6) (h' : k = Real.sin (2 * θ)) :
    k = 2 / 3 := by
    -- transform the equation
    have h2 : Real.sin θ ^ 6 + Real.cos θ ^ 6 = 1 - 3 / 4 * Real.sin (2 * θ) ^ 2 := by
        -- step by step, using sin^2 θ + cos^2 θ = 1
        calc _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * (Real.sin θ ^ 4 - Real.sin θ ^ 2 * Real.cos θ ^ 2 + Real.cos θ ^ 4) := by ring_nf
             _ = 1 * (Real.sin θ ^ 4 - Real.sin θ ^ 2 * Real.cos θ ^ 2 + Real.cos θ ^ 4) := by rw [Real.sin_sq_add_cos_sq θ]
             _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) ^ 2 - 3 * Real.sin θ ^ 2 * Real.cos θ ^ 2 := by ring_nf
             _ = 1 ^ 2 - 3 * Real.sin θ ^ 2 * Real.cos θ ^ 2 := by rw [Real.sin_sq_add_cos_sq θ]
             _ = 1 - 3 / 4 * (2 * Real.sin θ * Real.cos θ) ^ 2 := by ring_nf
             _ = 1 - 3 / 4 * Real.sin (2 * θ) ^ 2 := by rw [←Real.sin_two_mul θ]
    -- derive the equation of sin 2θ
    rw [h', h2] at h
    -- transform the equation
    replace h : (3 * Real.sin (2 * θ) - 2) * (Real.sin (2 * θ) + 2) = 0 := by linarith
    -- show that sin 2θ + 2 ≠ 0
    have h3 : Real.sin (2 * θ) + 2 ≠ 0 := by
        intro hsin
        replace hsin : -2 ∈ Set.range Real.sin := by
            simp [Set.range] -- use range(sin) = [-1, 1]
            use 2 * θ
            linarith
        simp at hsin
    -- solve the equation
    have h4 := (mul_eq_zero).mp h
    -- have 3 * sin 2θ - 2 = 0 or sin 2θ + 2 = 0
    rcases h4 with (h4 | h4)
    . linarith -- first case is the answer
    . contradiction -- second case is impossible
