import Mathlib

/- Find all functions $f$ from $\mathbb{R}$ to $\mathbb{R}$ such that for all real numbers $x$ and $y$:
$$
f(x f(y))+x=f(x) f(y+1)
$$ -/
theorem algebra_607709 (f : ℝ → ℝ) : (∀ x y, f (x * f y) + x = f x * f (y + 1)) ↔ (∀ x, f x = x) ∨ (∀ x, f x = -x) := by
    constructor
    .
        intro h
        -- First prove that f(0) = 0
        have h1 : f 0 = 0:= by
            -- For y = 0, we get f(0) = f(0) * f(y + 1)
            have h2 : ∀ y : ℝ, f 0 = f 0 * f (y + 1):= by
                intro y
                specialize h 0 y
                simp at h
                exact h
            -- Prove there exists some 'a' where f(a) ≠ 1
            have h3 : ∃ a : ℝ, f a ≠ 1:= by
                by_contra H
                simp at H
                simp [H] at h
                specialize h 1
                linarith
            rcases h3 with ⟨a, h3⟩
            specialize h2 (a - 1)
            ring_nf at h2
            -- Use this to prove f(0) = 0
            replace h3 : f a - 1 ≠ 0:= by exact sub_ne_zero_of_ne h3
            replace h2 : (f a - 1) * f 0 = 0:= by linarith
            exact eq_zero_of_ne_zero_of_mul_left_eq_zero h3 h2

        -- Prove that for all x, x = f(x) * f(1)
        have h2 : ∀ x : ℝ, x = (f x) * (f 1):= by
            intro x
            specialize h x 0
            simp at h
            rw [h1] at h
            simp at h
            rw [h1] at h
            simp at h
            exact h

        -- Use x = 1 to show f(1) must be either 1 or -1
        have h3:= h2 1
        replace h3 : (f 1 - 1) * (f 1 + 1) = 0:= by linarith
        replace h3 : f 1 - 1 = 0 ∨ f 1 + 1 = 0:= by exact eq_zero_or_eq_zero_of_mul_eq_zero h3
        rcases h3 with h3 | h3
        .
            -- Case f(1) = 1: proves f(x) = x for all x
            left
            intro x
            replace h3 : f 1 = 1:= by linarith
            rw [h3] at h2
            specialize h2 x
            linarith
        .
            -- Case f(1) = -1: proves f(x) = -x for all x
            right
            intro x
            specialize h2 x
            replace h3 : f 1 = -1:= by linarith
            rw [h3] at h2
            linarith
    .
        -- Prove the reverse implication: if f(x) = x or f(x) = -x, then the functional equation holds
        intro h
        rcases h with h | h
        all_goals
        simp [h]
        intro x y
        linarith
