import Mathlib
/- Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ die voldoen aan

$$
f(x) f(y)=f(x+y)+x y
$$

voor alle $x, y \in \mathbb{R}$. -/
theorem algebra_604165 {f : ℝ → ℝ} : (∀ x y, f x * f y = f (x + y) + x * y) ↔
(∀ x, f x = -x + 1) ∨ (∀ x, f x = x + 1):= by
    constructor
    -- Forward direction: assuming the functional equation holds
    .
        intro h
        -- Prove that there exists a value 'a' where f(a) ≠ 0
        have h1 : ∃ a : ℝ, f a ≠ 0:= by
            by_contra H
            simp at H
            simp [H] at h
            specialize h 1 1
            simp at h
        rcases h1 with ⟨a, ha⟩
        -- Prove that f(0) = 1
        have h1 : f 0 = 1:= by
            specialize h a 0
            simp at h
            replace h : f a * (f 0 - 1) = 0:= by linarith
            simp [ha] at h
            linarith
        -- Prove that either f(1) = 0 or f(-1) = 0
        have h2 : f 1 = 0 ∨ f (-1) = 0:= by
            specialize h 1 (-1)
            simp at h
            rw [h1] at h
            simp at h
            exact h
        rcases h2 with h2 | h2
        -- Case 1: if f(1) = 0, then f(x) = -x + 1
        .
            left
            intro x
            specialize h 1 (x - 1)
            simp at h
            rw [h2] at h
            simp at h
            linarith
        -- Case 2: if f(-1) = 0, then f(x) = x + 1
        .
            right
            intro x
            specialize h (-1) (x + 1)
            simp at h
            rw [h2] at h
            simp at h
            linarith
    -- Backward direction: proving that either form of f satisfies the equation
    .
        intro h
        rcases h with h | h
        all_goals
            simp [h]
            intro x y
            linarith
