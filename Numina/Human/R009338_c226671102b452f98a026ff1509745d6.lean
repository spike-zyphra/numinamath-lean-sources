import Mathlib
/- Find all functions $f: \mathbf{R} \rightarrow \mathbf{R}$ such that

$$
f\left(x^{2}+y f(z)\right)=x f(x)+z f(y)
$$

for all $x, y, z$ in $\mathbf{R}$. (Here $\mathbf{R}$ denotes the set of all real numbers.) -/
theorem algebra_607820 (f : ℝ → ℝ) :
    -- The theorem states that f satisfies the functional equation if and only if
    -- f is either the zero function or the identity function
    (∀ x y z, f (x ^ 2 + y * f z) = x * f x + z * f y) ↔
    (∀ x, f x = 0) ∨ (∀ x, f x = x):= by
        constructor
        . -- Forward direction: if f satisfies the equation, then it's either zero or identity
            intro h
            -- First, prove that f(0) = 0 by setting x=y=0, z=2 in the original equation
            have h1 : f 0 = 0:= by
                specialize h 0 0 2
                simp at h
                linarith
            -- Next, prove that f(f(z)) = z*f(1) for all z by setting x=0, y=1
            have h2 : ∀ z : ℝ, f (f z) = z * f 1:= by
                intro z
                specialize h 0 1 z
                simp at h
                exact h
            -- Prove that f(x*f(x)) = x²*f(1) for all x
            have h3 : ∀ x : ℝ, f (x * f x) = x ^ 2 * f 1:= by
                intro x
                specialize h x 0 1
                rw [h1] at h
                simp at h
                specialize h2 (x ^ 2)
                rw [←h, h2]
            -- Prove that f(x*f(x)) = x*f(x) for all x
            have h4 : ∀ x : ℝ, f (x * f x) = x * f x:= by
                intro x
                specialize h 0 x x
                simp at h
                exact h
            -- Case split on whether f(1) = 0
            by_cases h5 : f 1 = 0
            . -- If f(1) = 0, prove f is the zero function
                left
                intro x
                by_cases h6 : x = 0
                .
                    rw [h6, h1]
                .
                    specialize h3 x
                    specialize h4 x
                    rw [h3, h5] at h4
                    simp [h6] at h4
                    exact h4
            . -- If f(1) ≠ 0, prove f is the identity function
                -- First show that f(x) = x*f(1) for all x
                have h6 : ∀ x : ℝ, f x = x * f 1:= by
                    intro x
                    by_cases h7 : x = 0
                    .
                        subst x
                        simp [h1]
                    .
                        specialize h3 x
                        specialize h4 x
                        rw [h3] at h4
                        replace h4 : x * (x * f 1 - f x) = 0:= by linarith
                        replace h4 : x * f 1 - f x = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h7 h4
                        linarith
                -- Then prove that f(1) = 1
                specialize h 0 1 1
                simp at h
                have g1:= h6 (f 1)
                simp at g1
                rw [g1] at h
                replace h : f 1 * (f 1 - 1) = 0:= by linarith
                replace h : f 1 - 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h5 h
                -- Finally conclude f is the identity function
                right
                intro x
                specialize h6 x
                replace h : f 1 = 1:= by linarith
                rw [h] at h6
                simp at h6
                exact h6
        . -- Backward direction: verify that either function satisfies the equation
            intro h
            rcases h with h | h
            . -- Case: f is the zero function
                simp [h]
            . -- Case: f is the identity function
                simp [h]
                intro x y z
                linarith
