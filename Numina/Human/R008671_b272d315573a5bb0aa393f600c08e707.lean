import Mathlib
/- Problem: Determine all functions f from ℝ to ℝ such that for all real x and y:
   f(x+y) = f(x-y) + f(f(1-xy)) -/
theorem algebra_605150 (f : ℝ → ℝ) : (∀ x y, f (x + y) = f (x - y) + f (f (1 - x * y))) ↔ ∀ x, f x = 0 := by
    constructor
    .
        intro h
        -- First, prove that f(f(1)) = 0 by setting x = y = 0
        have h1 : f (f 1) = 0:= by
            specialize h 0 0
            ring_nf at h
            linarith
        -- Prove that f is an even function: f(y) = f(-y)
        have h2 : ∀ y : ℝ, f y = f (-y):= by
            intro y
            specialize h 0 y
            simp at h
            linarith
        -- Special case when y = 1: f(x+1) = f(x-1) + f(f(1-x))
        have h3 : ∀ x : ℝ, f (x + 1) = f (x - 1) + f (f (1 - x)):= by
            intro x
            specialize h x 1
            simp at h
            linarith
        -- Another key equation by substituting -x+2 into h3
        have h4 : ∀ x : ℝ, f (-x + 3) = f (-x + 1) + f (f (x - 1)):= by
            intro x
            specialize h3 (-x + 2)
            ring_nf at h3
            ring_nf
            linarith
        -- Prove that f(x+1) = f(-x+3)
        replace h4 : ∀ x : ℝ, f (x + 1) = f (-x + 3):= by
            intro x
            specialize h3 x
            specialize h4 x
            have g1:= h2 (x - 1)
            simp at g1
            rw [g1] at h3 h4
            rw [show -x + 1 = 1 - x by ring] at h4
            linarith
        -- Prove that f(x+2) = f(x-2)
        replace h4 : ∀ x : ℝ, f (x + 2) = f (x - 2):= by
            intro x
            specialize h4 (x + 1)
            ring_nf at h4
            specialize h2 (x - 2)
            simp at h2
            rw [h2, ←h4]
            ring_nf
        -- Prove that f(f(1-2x)) = 0
        have h5 : ∀ x : ℝ, f (f (1 - x * 2)) = 0:= by
            intro x
            specialize h x 2
            specialize h4 x
            linarith
        -- Prove that f(f(x)) = 0 for all x
        replace h5 : ∀ x : ℝ, f (f x) = 0:= by
            intro x
            specialize h5 ((1 - x) / 2)
            ring_nf at h5
            rw [h5]
        -- Prove that f is constant: f(x) = f(0) for all x
        have h6 : ∀ x : ℝ, f x = f 0:= by
            intro x
            specialize h (x / 2) (x / 2)
            ring_nf at h
            specialize h5 (1 + x ^ 2 * (-1 / 4))
            rw [h5] at h
            linarith
        -- Finally prove that f(x) = 0 for all x
        intro x
        have h7:= h6 x
        rw [h7]
        specialize h6 (f 1)
        rw [←h6, h1]
    .
        -- The reverse direction is trivial: if f is constantly 0, it satisfies the equation
        intro h
        simp [h]
