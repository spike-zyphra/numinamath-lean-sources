import Mathlib

/- If we express $-2x^2 + 4x + 5$ in the form $a(x - h)^2 + k$, then what is $k$? -/
theorem algebra_19686 {a h k : ℝ} (ha : a ≠ 0) (hform : ∀ x, -2 * x ^ 2 + 4 * x + 5 = a * (x - h) ^ 2 + k) :
    k = 7 := by
    -- specialize at x = 0
    have h1 : 5 = a * h ^ 2 + k := by
        specialize hform 0
        ring_nf at hform ⊢
        exact hform
    -- specialize at x = 1
    have h2 : 7 = a * (1 - h) ^ 2 + k := by
        specialize hform 1
        ring_nf at hform ⊢
        exact hform
    -- specialize at x = -1
    have h3 : -1 = a * (-1 - h) ^ 2 + k := by
        specialize hform (-1)
        ring_nf at hform ⊢
        exact hform
    -- solve the system of equations
    have h4 : a = -2 := by linarith
    have h5 : h = 1 := by nlinarith
    -- substitute back
    rw [h4, h5] at h1
    -- derive the result
    linarith
