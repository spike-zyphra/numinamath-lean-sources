import Mathlib

/- Trouver toutes les fonctions $f: \mathbb{R} \rightarrow \mathbb{R}$ telles que, pour tous $x$ et $y$,

$$
f(x y) \leqslant x f(y)
$$ -/
theorem algebra_607471 (f : ℝ → ℝ) : (∀ x y : ℝ, f (x * y) ≤ x * f y) ↔ ∃ a b : ℝ, a ≥ b ∧ (∀ x : ℝ, x ≤ 0 → f x = a * x) ∧ (∀ x : ℝ, x ≥ 0 → f x = b * x):= by
    constructor
    .
    -- Forward direction: assuming f(xy) ≤ x*f(y), prove the existence of a,b
        intro h
        -- First prove f(0) = 0 using x = 0, y = 0 and x = 2, y = 0
        have h1 : f 0 = 0:= by
            have g1:= h 0 0
            have g2:= h 2 0
            simp at g1 g2
            linarith
        -- Key lemma: f(x)/x = f(y)/y when x,y are either both positive or both negative
        have h2 : ∀ x y : ℝ, (x > 0 ∧ y > 0) ∨ (x < 0 ∧ y < 0) → f x / x = f y / y:= by
            intro x y hxy
            have g1:= h (x / y) y
            have g2:= h (y / x) x
            rcases hxy with hxy | hxy
            -- Case: both x,y > 0
            .
                rcases hxy with ⟨hx, hy⟩
                rw [show x / y * y = x by field_simp] at g1
                rw [show y / x * x = y by field_simp] at g2
                rw [show x / y * f y = x * (f y / y) by ring] at g1
                replace g1 : f x / x ≤ f y / y:= by exact (div_le_iff₀' hx).mpr g1
                rw [show y / x * f x = y * (f x / x) by ring] at g2
                replace g2 : f y / y ≤ f x / x:= by exact (div_le_iff₀' hy).mpr g2
                linarith
            -- Case: both x,y < 0
            .
                rcases hxy with ⟨hx, hy⟩
                have gx : x ≠ 0:= by linarith
                have gy : y ≠ 0:= by linarith
                rw [show x / y * y = x by field_simp] at g1
                rw [show y / x * x = y by field_simp] at g2
                rw [show x / y * f y = x * (f y / y) by ring] at g1
                rw [show y / x * f x = y * (f x / x) by ring] at g2
                replace g1 : f x / x ≥ f y / y:= by exact (le_div_iff_of_neg' hx).mpr g1
                replace g2 : f y / y ≥ f x / x:= by exact (le_div_iff_of_neg' hy).mpr g2
                linarith
        -- For x ≥ 0, f(x) = f(1)*x
        have h3 : ∀ x : ℝ, x ≥ 0 → f x = f 1 * x:= by
            intro x hx
            by_cases hx0 : x = 0
            .
                subst x
                simp
                exact h1
            .
                replace hx : x > 0:= by positivity
                clear hx0
                specialize h2 x 1 (Or.inl ⟨hx, (by linarith)⟩)
                field_simp at h2
                linarith
        -- For x ≤ 0, f(x) = -f(-1)*x
        have h4 : ∀ x : ℝ, x ≤ 0 → f x = -f (-1) * x:= by
            intro x hx
            by_cases hx0 : x = 0
            .
                subst x
                simp
                exact h1
            .
                replace hx : x < 0:= by
                    by_contra H
                    simp at H
                    replace H : x = 0:= by linarith
                    trivial
                specialize h2 x (-1) (Or.inr ⟨hx, (by linarith)⟩)
                field_simp at h2
                linarith
        -- Prove -f(-1) ≥ f(1)
        have h5 : -f (-1) ≥ f 1:= by
            specialize h (-1) (-1)
            simp at h
            linarith
        -- Let a = -f(-1)
        use (-f (-1))
        -- Let b = f(1)
        use (f 1)
    -- Backward direction: assuming existence of a,b, prove f(xy) ≤ x*f(y)
    .
        intro h
        rcases h with ⟨a, b, hab, h3, h4⟩
        intro x y
        by_cases hx : x ≥ 0
        -- Case: x ≥ 0
        .
            by_cases hy : y ≥ 0
            -- Subcase: y ≥ 0
            .
                have h5:= h4 (x * y) (by positivity)
                specialize h4 y hy
                rw [h4, h5]
                suffices x * y * (a - b) ≥ 0 by linarith
                replace hab : a - b ≥ 0:= by linarith
                positivity
            -- Subcase: y < 0
            .
                simp at hy
                have h5:= h3 (x * y) (by nlinarith only [hx, hy])
                specialize h3 y (by linarith)
                rw [h3, h5]
                suffices x * (-y) * (a - b) ≥ 0 by linarith
                replace hy : -y > 0:= by linarith
                replace hab : a - b ≥ 0:= by linarith
                positivity
        -- Case: x < 0
        .
            by_cases hy : y ≥ 0
            -- Subcase: y ≥ 0
            .
                simp at hx
                have h5:= h3 (x * y) (by nlinarith only [hx, hy])
                specialize h4 y hy
                rw [h4, h5]
                suffices (-x) * y * (a - b) ≥ 0 by linarith
                replace hx : -x > 0:= by linarith
                replace hab : a - b ≥ 0:= by linarith
                positivity
            -- Subcase: y < 0
            .
                simp at hx hy
                have h5:= h4 (x * y) (by nlinarith only [hx, hy])
                specialize h3 y (by linarith)
                rw [h3, h5]
                replace hx : -x > 0:= by linarith
                replace hy : -y > 0:= by linarith
                replace hab : a - b ≥ 0:= by linarith
                suffices (-x) * (-y) * (a - b) ≥ 0 by linarith
                positivity
