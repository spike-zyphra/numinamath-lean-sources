import Mathlib
/- Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ die voldoen aan

$$
f(x+y f(x))=f(x f(y))-x+f(y+f(x))
$$

voor alle $x, y \in \mathbb{R}$. -/
theorem algebra_605011 {f : ℝ → ℝ} : (∀ x y, f (x + y * f x) = f (x * f y) - x + f (y + f x)) ↔
∀ x, f x = 1 - x:= by
    constructor
    .
        intro h
        -- Proves that f(f(0)) = 0 using x = y = 0 in the original equation
        have h1 : f (f 0) = 0:= by
            specialize h 0 0
            simp at h
            exact h
        -- Proves that f(f(1)) = 1 using x = y = 1
        have h2 : f (f 1) = 1:= by
            specialize h 1 1
            simp at h
            linarith
        -- Proves that f(1) = 0 using x = 1, y = 0
        replace h1 : f 1 = 0:= by
            specialize h 1 0
            simp at h
            rw [h1, h2] at h
            linarith
        rw [h1] at h2
        -- Proves that f(f(x)) = x for all x ∈ ℝ
        have h3 : ∀ x : ℝ, f (f x) = x:= by
            intro x
            specialize h x 0
            simp at h
            rw [h2] at h
            simp at h
            linarith
        -- Proves that f(1) = f(f(y)) - 1 + f(y) for all y ∈ ℝ
        have h4 : ∀ y : ℝ, f 1 = f (f y) - 1 + f y:= by
            intro y
            specialize h 1 y
            simp at h
            rw [h1] at h
            simp at h
            exact h
        intro x
        specialize h3 x
        specialize h4 x
        rw [h3] at h4
        linarith
    .
        -- Proves the reverse implication: if f(x) = 1-x, then it satisfies the original equation
        intro h
        simp [h]
        intro x y
        linarith
