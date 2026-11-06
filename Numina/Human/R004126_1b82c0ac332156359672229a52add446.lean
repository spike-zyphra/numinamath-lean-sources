import Mathlib
/- Determine all functions $f$ from the real numbers to the real numbers, different from the zero function, such that $f(x) f(y)=f(x-y)$ for all real numbers $x$ and $y$. -/
theorem algebra_238755 (f : ℝ → ℝ) (h : ∃ x, f x ≠ 0) :
(∀ x y, f x * f y = f (x - y)) ↔ ∀ x, f x = 1:= by
    -- Extract the witness point where f is non-zero
    rcases h with ⟨a, ha⟩
    constructor
    .
        intro h
        -- First prove that f(0) = 1
        have h1 : f 0 = 1:= by
            specialize h a 0
            simp at h
            replace h : f a * (f 0 - 1) = 0:= by linarith
            simp [ha] at h
            linarith
        -- Then prove that f is nowhere zero
        have h2 : ∀ x : ℝ, f x ≠ 0:= by
            intro x
            specialize h x x
            ring_nf at h
            rw [h1] at h
            by_contra H
            rw [H] at h
            simp at h
        -- Finally prove that f is constantly 1
        intro x
        specialize h x (x / 2)
        ring_nf at h
        replace h : f (x * (1 / 2)) * (f x - 1) = 0:= by linarith
        simp [h2 (x * 2 ⁻¹)] at h
        linarith
    .
        -- The reverse direction is trivial
        intro h
        simp [h]
