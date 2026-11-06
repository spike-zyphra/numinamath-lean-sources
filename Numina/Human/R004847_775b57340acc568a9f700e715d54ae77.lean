import Mathlib
/- Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that

$$
(x-y)(f(x)+f(y)) \leqslant f\left(x^{2}-y^{2}\right) \quad \text { for all } x, y \in \mathbb{R}
$$

# -/
theorem algebra_604209 (f : ℝ → ℝ) :
(∀ x y, (x - y) * (f x + f y) ≤ f (x ^ 2 - y ^ 2)) ↔ ∃ c, ∀ x, f x = c * x:= by
    constructor
    -- Forward direction: proving that the inequality implies f(x) = cx
    .
        intro h
        -- First prove that f(0) = 0
        have h1 : f 0 = 0:= by
            have g1:= h 1 0
            have g2:= h 0 0
            simp at g1 g2
            linarith
        -- Prove that f is odd: f(-x) = -f(x)
        have h2 : ∀ x : ℝ, f (-x) = -f x:= by
            intro x
            by_cases hx : x = 0
            .
                subst x
                simp
                linarith
            .
                have g1:= h x (-x)
                have g2:= h (-x) x
                simp at g1 g2
                rw [h1] at g1 g2
                have g3 : x * (f x + f (-x)) = 0:= by linarith
                simp [hx] at g3
                linarith
        -- Prove that the inequality is actually an equality
        have h3 : ∀ x y : ℝ, (x - y) * (f x + f y) = f (x ^ 2 - y ^ 2):= by
            intro x y
            have g1:= h x y
            have g2:= h y x
            specialize h2 (y ^ 2 - x ^ 2)
            rw [show -(y ^ 2 - x ^ 2) = x ^ 2 - y ^ 2 by ring] at h2
            linarith
        -- Prove that f(x)y = f(y)x for all x,y
        have h4 : ∀ x y : ℝ, f x * y = f y * x:= by
            intro x y
            have g1:= h3 x y
            have g2:= h3 x (-y)
            simp at g1 g2
            specialize h2 y
            rw [h2] at g2
            linarith
        -- Conclude that f(x) = cx where c = f(1)
        use (f 1)
        intro x
        specialize h4 x 1
        simp at h4
        exact h4
    -- Backward direction: proving that f(x) = cx satisfies the inequality
    .
        intro h
        rcases h with ⟨c, hc⟩
        simp [hc]
        intro x y
        linarith
