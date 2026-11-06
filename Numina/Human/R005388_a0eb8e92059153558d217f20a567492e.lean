import Mathlib
/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
f(f(x) f(y)+y)=f(x) y+f(y-x+1)
$$

for all $x, y \in \mathbb{R}$. -/
theorem algebra_608046 (f : ℝ → ℝ) : (∀ x y, f (f x * f y + y) = f x * y + f (y - x + 1)) ↔
(∀ x, f x = 0) ∨ (∀ x, f x = 1 - x) ∨ (∀ x, f x = x - 1):= by
    constructor
    .
        intro h
        -- Helper lemma: If f satisfies the equation and f(0) ≥ 0, then f is either constant 0 or f(x) = 1-x
        have h0 : ∀ f : ℝ → ℝ, (∀ x y, f (f x * f y + y) = f x * y + f (y - x + 1)) ∧ f 0 ≥ 0 → (∀ x, f x = 0) ∨ (∀ x, f x = 1 - x):= by
            intro f ⟨h, h1⟩
            -- Case split: Either f is periodic for some non-zero period, or f is injective
            by_cases h2 : ∃ t : ℝ, t ≠ 0 ∧ (∃ a : ℝ, f (a + t) = f a)
            .
                -- Case 1: f has a period t ≠ 0
                rcases h2 with ⟨t, ht, ht2⟩
                rcases ht2 with ⟨a, ha⟩
                -- Show that f is periodic with period t
                have h3 : ∀ y : ℝ, f (y - a + 1) = f (y - (a + t) + 1):= by
                    intro y
                    have g1:= h a y
                    have g2:= h (a + t) y
                    rw [ha] at g2
                    linarith
                replace h3 : ∀ y : ℝ, f (y + t) = f y:= by
                    intro y
                    specialize h3 (y + t + a - 1)
                    ring_nf at h3
                    exact h3
                -- Prove f is constant 0
                left
                intro x
                have g1:= h x t
                have g2:= h x 0
                have g3:= h3 0
                simp at g3
                rw [g3] at g1
                rw [h3 (f x * f 0)] at g1
                simp at g1 g2
                rw [←h3 (-x + 1)] at g2
                ring_nf at g1 g2
                replace g1 : f x * t = 0:= by linarith
                simp [ht] at g1
                exact g1
            .
                -- Case 2: f is injective
                simp at h2
                replace h2 : ∀ x y : ℝ, f x = f y → x = y:= by
                    intro x y hxy
                    by_contra H
                    replace H : x - y ≠ 0:= by exact sub_ne_zero_of_ne H
                    specialize h2 (x - y) H y
                    ring_nf at h2
                    trivial
                -- Show that f(x)f(0) = 1-x
                have h3 : ∀ x : ℝ, f x * f 0 = 1 - x:= by
                    intro x
                    specialize h x 0
                    simp at h
                    specialize h2 (f x * f 0) (-x + 1) h
                    linarith
                -- Prove f(0) = 1
                replace h1 : f 0 = 1:= by
                    specialize h3 0
                    simp at h3
                    replace h3 : (f 0 + 1) * (f 0 - 1) = 0:= by linarith
                    have g1 : f 0 + 1 ≠ 0:= by linarith
                    simp [g1] at h3
                    linarith
                rw [h1] at h3
                -- Conclude f(x) = 1-x
                right
                intro x
                specialize h3 x
                linarith
        -- Main case split based on f(0) ≥ 0
        by_cases h1 : f 0 ≥ 0
        .
            -- Case: f(0) ≥ 0
            specialize h0 f ⟨h, h1⟩
            rcases h0 with h0 | h0
            .
                left
                simp [h0]
            .
                right
                left
                simp [h0]
        .
            -- Case: f(0) < 0, consider -f instead
            set g:= -f with hg
            replace h : ∀ x y, g (g x * g y + y) = g x * y + g (y - x + 1):= by
                intro x y
                simp [hg]
                specialize h x y
                linarith
            simp at h1
            replace h1 : g 0 ≥ 0:= by
                simp [hg]
                linarith
            specialize h0 g ⟨h, h1⟩
            rcases h0 with h0 | h0
            .
                simp [hg] at h0
                left
                simp [h0]
            .
                right
                right
                simp [hg] at h0
                intro x
                specialize h0 x
                linarith
    .
        -- Reverse implication: verify each solution satisfies the equation
        intro h
        rcases h with h | h | h
        .
            simp [h]
        .
            simp [h]
            intro x y
            linarith
        .
            simp [h]
            intro x y
            linarith
