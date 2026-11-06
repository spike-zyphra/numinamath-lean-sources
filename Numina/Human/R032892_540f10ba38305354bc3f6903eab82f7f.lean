import Mathlib
/- Man bestimme alle Funktionen $f: \mathbb{Z} \rightarrow \mathbb{Z}$, die für alle $x, y \in \mathbb{Z}$ die Gleichung $f(x-f(y))=f(f(x))-f(y)-1$
erfüllen. -/
theorem algebra_605040 (f : ℤ → ℤ) : (∀ x y, f (x - f y) = f (f x) - f y - 1) ↔ (∀ x, f x = -1) ∨ (∀ x, f x = x + 1) := by
    constructor
    .
        intro h
        -- Let z = -f(f(0)) for later use
        set z:= -f (f 0) with hz
        clear_value z
        -- Prove that f(z) = -1 using the original equation with x=0, y=f(0)
        have h1 : f z = -1:= by
            specialize h 0 (f 0)
            simp at h
            rw [←hz] at h
            exact h
        -- Prove that for all x, f(x+1) = f(f(x))
        have h2 : ∀ x : ℤ, f (x + 1) = f (f x):= by
            intro x
            specialize h x z
            rw [h1] at h
            ring_nf at h
            ring_nf
            exact h
        -- Rewrite the original equation using h2
        replace h : ∀ x y : ℤ, f (x - f y) = f (x + 1) - f y - 1:= by
            intro x y
            specialize h x y
            rw [←(h2 x)] at h
            exact h
        -- Derive a relationship between consecutive values of f
        have h3 : ∀ x : ℤ, f (x + 1) - f x = f (f (x - 1 - f x)) + 1:= by
            intro x
            specialize h x x
            specialize h2 (x - 1 - f x)
            ring_nf at h h2
            ring_nf
            linarith
        -- Prove that the difference between consecutive values is constant
        have h4 : ∀ x : ℤ, f (x + 1) = f x + (f (-1) + 1):= by
            intro x
            specialize h3 x
            specialize h (x - 1) x
            ring_nf at h h3
            rw [h] at h3
            ring_nf
            linarith
        -- Let d be the constant difference f(-1) + 1
        set d:= f (-1) + 1 with hc
        clear_value d
        -- Prove that f follows an arithmetic sequence with difference d
        replace h4 : ∀ n : ℤ, ∀ m : ℕ, f (n + m) = f n + m * d:= by
            intro n m
            induction m with
            | zero =>
                simp
            | succ m ih =>
                simp
                specialize h4 (n + m)
                rw [show n + (m + 1) = n + m + 1 by omega]
                rw [h4, ih]
                linarith
        -- Prove that f(n) = n*d + f(0) for all integers n
        replace h4 : ∀ n : ℤ, f n = n * d + f 0:= by
            intro n
            by_cases h : n > 0
            .
                specialize h4 0 (n.natAbs)
                simp at h4
                rw [show |n| = n by exact abs_of_pos h] at h4
                linarith
            .
                simp at h
                by_cases h : n < 0
                .
                    specialize h4 n ((-n).natAbs)
                    simp at h4
                    rw [show |n| = -n by exact abs_of_neg h] at h4
                    simp at h4
                    linarith
                .
                    replace h : n = 0:= by omega
                    subst n
                    simp
        -- Let b = f(0)
        set b:= f 0 with hb
        clear_value b
        simp [h4] at h
        -- Use the original equation to derive constraints on d
        have g1:= h 0 1
        have g2:= h 1 0
        ring_nf at g1 g2
        -- Prove that d(d-1) = 0, so d = 0 or d = 1
        have g3 : d * (d - 1) = 0:= by linarith
        replace g3 : d = 0 ∨ d - 1 = 0:= by exact Int.mul_eq_zero.mp g3
        rcases g3 with g3 | g3
        .
            -- Case d = 0: Proves f(x) = -1 for all x
            rw [g3] at g2
            simp at g2
            rw [g2, g3] at h4
            simp at h4
            simp [h4]
        .
            -- Case d = 1: Proves f(x) = x + 1 for all x
            replace g3 : d = 1:= by omega
            rw [g3] at h4
            have g4:= h4 b
            ring_nf at g4
            have g5:= h4 z
            rw [h1] at g5
            rw [hz, g4] at g5
            ring_nf at g5
            replace g5 : b = 1:= by linarith
            right
            rw [g5] at h4
            simp at h4
            exact h4
    .
        -- Prove that both f(x) = -1 and f(x) = x + 1 satisfy the original equation
        intro h
        rcases h with h | h
        .
            simp [h]
        .
            simp [h]
            intro x y
            linarith
