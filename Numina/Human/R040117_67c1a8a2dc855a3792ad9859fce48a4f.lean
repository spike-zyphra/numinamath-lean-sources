import Mathlib
/- Trouver toutes les fonctions f de $\mathbb{R}$ dans $\mathbb{R}$ telles que pour tous réels $x, y$,

$$
f(x) f(y)=f(x y)+x+y
$$ -/
theorem algebra_607257 (f : ℝ → ℝ) : (∀ x y, f x * f y = f (x * y) + x + y) ↔ ∀ x, f x = 1 + x := by
    constructor
    -- Forward direction: assuming the functional equation, prove f(x) = 1 + x
    .
        intro h
        -- First prove that f(0) ≠ 0 by contradiction
        have h1 : f 0 ≠ 0:= by
            by_contra H
            specialize h 1 0
            simp at h
            rw [H] at h
            simp at h
        -- Then prove that f(0) = 1
        replace h1 : f 0 = 1:= by
            specialize h 0 0
            simp at h
            replace h : f 0 * (f 0 - 1) = 0:= by linarith
            replace h : f 0 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h1 h
            linarith
        -- Finally prove that f(x) = 1 + x for all x
        intro x
        specialize h x 0
        simp at h
        rw [h1] at h
        simp at h
        exact h
    -- Backward direction: prove that f(x) = 1 + x satisfies the functional equation
    .
        intro h
        simp [h]
        intro x y
        linarith
