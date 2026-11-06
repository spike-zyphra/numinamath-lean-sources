import Mathlib
/- Find all functions $f: \mathbf{R} \rightarrow \mathbf{R}$ such that

$$
f(x+y) f(x-y)=(f(x)+f(y))^{2}-4 x^{2} f(y)
$$

for all $x, y \in \mathbf{R}$, where $\mathbf{R}$ denotes the set of all real numbers. -/

theorem algebra_607855 (f : ℝ → ℝ) : (∀ x y : ℝ, f (x + y) * f (x - y) = (f x + f y) ^ 2 - 4 * x ^ 2 * f y) ↔
(∀ x : ℝ, f x = 0) ∨ (∀ x : ℝ, f x = x ^ 2):= by
    constructor
    .
        intro h
        -- First prove that f(0) = 0
        have h1 : f 0 = 0:= by
            specialize h 0 0
            ring_nf at h
            replace h : f 0 ^ 2 = 0:= by linarith
            simp at h
            exact h
        -- For any x, prove that f(x) is either 0 or x^2
        have h2 : ∀ x : ℝ, f x = 0 ∨ f x = x ^ 2:= by
            intro x
            specialize h x x
            ring_nf at h
            rw [h1] at h
            simp at h
            replace h : f x * (f x - x ^ 2) = 0:= by linarith
            simp at h
            rcases h with h | h
            .
                left
                exact h
            .
                right
                linarith
        -- Case analysis: either f is identically zero or not
        by_cases ha : ∀ x : ℝ, f x = 0
        .
            simp [ha]
        .
            simp at ha
            rcases ha with ⟨a, ha⟩
            -- Prove that a ≠ 0
            have hane : a ≠ 0:= by
                by_contra H
                subst a
                trivial
            -- Show that f(a) = a^2
            have ha1 : f a = a ^ 2:= by
                specialize h2 a
                simp [ha] at h2
                exact h2
            -- Check if f(x) = x^2 for all x ≠ 0
            by_cases hb : ∀ x : ℝ, x ≠ 0 → f x = x ^ 2
            .
                -- If true, then f(x) = x^2 for all x (including x = 0)
                right
                intro x
                by_cases hx : x = 0
                .
                    -- Handle the case where x = 0
                    subst x
                    rw [h1]
                    simp
                .
                    -- Handle the case where x ≠ 0
                    specialize hb x hx
                    rw [hb]
            .
                -- If not, then there exists a b ≠ 0 where f(b) ≠ b^2
                simp at hb
                rcases hb with ⟨b, hbne, hb⟩
                -- Show that f(b) must be 0
                have hb1 : f b = 0:= by
                    specialize h2 b
                    simp [hb] at h2
                    exact h2
                -- Prove that b must be equal to either √2 * a or -√2 * a
                have h3 : b = √2 * a ∨ b = -√2 * a:= by
                    specialize h a b
                    rw [hb1, ha1] at h
                    simp at h
                    -- Show that (a^2)^2 is nonzero
                    have g1 : (a ^ 2) ^ 2 ≠ 0:= by positivity
                    rw [←h] at g1
                    simp at g1
                    -- Check f values at a+b and a-b
                    have g2:= h2 (a + b)
                    have g3:= h2 (a - b)
                    rcases g1 with ⟨gab, gba⟩
                    simp [gab] at g2
                    simp [gba] at g3
                    rw [g2, g3] at h
                    -- Simplify to show b = ±√2 * a
                    replace h : b ^ 2 * (b ^ 2 - 2 * a ^ 2) = 0:= by linarith
                    simp [hbne] at h
                    replace h : (b - √2 * a) * (b + √2 * a) = 0:= by
                        ring_nf
                        field_simp
                        linarith
                    simp at h
                    rcases h with h | h
                    .
                        left
                        linarith
                    .
                        right
                        linarith
                -- Handle both possible cases for b
                rcases h3 with h3 | h3
                .
                    -- Case 1: b = √2 * a
                    specialize h b a
                    subst b
                    ring_nf at h
                    field_simp at h
                    rw [ha1, hb1] at h
                    ring_nf at h
                    -- Show contradiction through a^4 = 0
                    have g1 : -(a ^ 4 * 7) ≠ 0:= by
                        by_contra H
                        simp at H
                        trivial
                    rw [←h] at g1
                    simp at g1
                    have g2:= h2 (√2 * a + a)
                    have g3:= h2 (√2 * a - a)
                    rcases g1 with ⟨gab, gba⟩
                    simp [gab] at g2
                    simp [gba] at g3
                    rw [g2, g3] at h
                    ring_nf at h
                    field_simp at h
                    ring_nf at h
                    rw [show √2 ^ 4 = (√2 ^ 2) ^ 2 by ring] at h
                    field_simp at h
                    ring_nf at h
                    replace h : a ^ 4 = 0:= by linarith
                    simp at h
                    by_contra _
                    trivial
                .
                    -- Case 2: b = -√2 * a (similar contradiction)
                    specialize h b a
                    subst b
                    rw [ha1, hb1] at h
                    ring_nf at h
                    field_simp at h
                    ring_nf at h
                    have g2:= h2 (-(√2 * a) + a)
                    have g3:= h2 (-(√2 * a) - a)
                    have g1 : -(a ^ 4 * 7) ≠ 0:= by
                        by_contra H
                        simp at H
                        trivial
                    rw [←h] at g1
                    simp at g1
                    rcases g1 with ⟨gab, gba⟩
                    simp [gab] at g2
                    simp [gba] at g3
                    rw [g2, g3] at h
                    ring_nf at h
                    rw [show √2 ^ 4 = (√2 ^ 2) ^ 2 by ring] at h
                    field_simp at h
                    ring_nf at h
                    replace h : a ^ 4 = 0:= by linarith
                    simp at h
                    by_contra _
                    trivial
    .
        intro h
        rcases h with h | h
        .
            simp [h]
        .
            simp [h]
            intro x y
            linarith
