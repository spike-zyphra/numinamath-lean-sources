import Mathlib
/- Trouver toutes les fonctions $f: \mathbb{R} \rightarrow \mathbb{R}$ telles que $f(x) f(y)-f(x y)=x+y$ pour tous $x, y \in \mathbb{R}$. -/
theorem algebra_607621 {f : ℝ → ℝ} : (∀ x y, f x * f y - f (x * y) = x + y) ↔
∀ x, f x = x + 1:= by
    constructor
    -- Forward direction: prove that if f satisfies the functional equation, then f(x) = x + 1
    .
        intro h
        -- First consider the case when x = y = 0
        have h1:= h 0 0
        simp at h1
        -- Rearrange to get f(0) * (f(0) - 1) = 0
        replace h1 : f 0 * (f 0 - 1) = 0:= by linarith
        simp at h1
        -- This means either f(0) = 0 or f(0) = 1
        rcases h1 with h1 | h1
        -- Case 1: f(0) = 0 leads to contradiction
        .
            specialize h 1 0
            simp at h
            rw [h1] at h
            by_contra _
            simp at h
        -- Case 2: f(0) = 1, which helps prove f(x) = x + 1
        .
            replace h1 : f 0 = 1:= by linarith
            intro x
            specialize h x 0
            simp at h
            rw [h1] at h
            simp at h
            linarith
    -- Backward direction: prove that if f(x) = x + 1, then it satisfies the functional equation
    .
        intro h
        simp [h]
        intro x y
        linarith
