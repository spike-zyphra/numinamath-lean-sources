import Mathlib
theorem algebra_608108 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c = 1) :
a * √(2 * b + 1) + b * √(2 * c + 1) + c * √(2 * a + 1) ≤ √(2 - (a ^ 2 + b ^ 2 + c ^ 2)) := by
-- Helper lemma: Cauchy-Schwarz inequality for 3D vectors
    have h1 : ∀ x1 y1 z1 x2 y2 z2 : ℝ, x1 > 0 → y1 > 0 → z1 > 0 → x2 > 0 → y2 > 0 → z2 > 0 →
        (x1 ^ 2 + y1 ^ 2 + z1 ^ 2) * (x2 ^ 2 + y2 ^ 2 + z2 ^ 2) ≥ (x1 * x2 + y1 * y2 + z1 * z2) ^ 2:= by
        intro x1 y1 z1 x2 y2 z2 _ _ _ _ _ _
        -- Uses the fact that sum of squares is non-negative
        have h1 : (x1 * y2 - y1 * x2) ^ 2 + (y1 * z2 - z1 * y2) ^ 2 + (z1 * x2 - x1 * z2) ^ 2 ≥ 0:= by positivity
        linarith

    -- Apply Cauchy-Schwarz to our specific vectors
    specialize h1 √(a * (2 * b + 1)) √(b * (2 * c + 1)) √(c * (2 * a + 1)) √a √b √c (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)

    -- Series of simplifications using square root properties
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1
    rw [Real.sq_sqrt (by positivity)] at h1

    -- Simplify expressions involving square roots
    rw [show √(a * (2 * b + 1)) = √a * √(2 * b + 1) by field_simp, show √a * √(2 * b + 1) * √a = √a ^ 2 * √(2 * b + 1) by ring_nf] at h1
    rw [show √(b * (2 * c + 1)) = √b * √(2 * c + 1) by field_simp, show √b * √(2 * c + 1) * √b = √b ^ 2 * √(2 * c + 1) by ring_nf] at h1
    rw [show √(c * (2 * a + 1)) = √c * √(2 * a + 1) by field_simp, show √c * √(2 * a + 1) * √c = √c ^ 2 * √(2 * a + 1) by ring_nf] at h1

    -- Further simplification
    rw [show √a ^ 2 = a by refine Real.sq_sqrt (by positivity)] at h1
    rw [show √b ^ 2 = b by refine Real.sq_sqrt (by positivity)] at h1
    rw [show √c ^ 2 = c by refine Real.sq_sqrt (by positivity)] at h1

    -- More algebraic manipulations
    have h2 : a * (2 * b + 1) + b * (2 * c + 1) + c * (2 * a + 1) ≤ 2 - (a ^ 2 + b ^ 2 + c ^ 2):= by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h]

    -- Final combination of all previous steps
    nlinarith [h1, h2, Real.sqrt_nonneg (a * (2 * b + 1)), Real.sqrt_nonneg (b * (2 * c + 1)), Real.sqrt_nonneg (c * (2 * a + 1)), Real.sqrt_nonneg (2 - (a ^ 2 + b ^ 2 + c ^ 2)), Real.sq_sqrt (show 0 ≤ (2 - (a ^ 2 + b ^ 2 + c ^ 2)) by nlinarith)]