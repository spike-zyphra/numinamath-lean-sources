import Mathlib
/- Одредити све функције $f: \mathbb{R} \rightarrow \mathbb{R}$ такве да за све $x, y \in \mathbb{R}$ важи

$$
f(x f(y)-y f(x))=f(x y)-x y . \quad \text { (Душан Ђукић) }
$$ -/
theorem algebra_608090 {f : ℝ → ℝ} : (∀ x y, f (x * f y - y * f x) = f (x * y) - x * y) ↔
    (∀ x, f x = x) ∨ (∀ x, f x = |x|) := by
    constructor
    . -- Forward direction: Given the functional equation, prove f(x) = x or f(x) = |x|
        intro h
        -- First prove f(0) = 0
        have h1 : f 0 = 0:= by
            have h1 : ∀ x : ℝ, f (x * f 0) = f 0:= by
                intro x
                specialize h x 0
                simp at h
                exact h
            by_contra H
            replace h1 : ∀ x : ℝ, f x = f 0:= by
                intro x
                specialize h1 (x / f 0)
                field_simp at h1
                exact h1
            simp [h1] at h
            specialize h 1 1
            linarith
        -- Prove f(x²) = x² for all x
        have h2 : ∀ x : ℝ, f (x ^ 2) = x ^ 2:= by
            intro x
            specialize h x x
            ring_nf at h
            rw [h1] at h
            linarith
        -- For all non-negative x, f(x) = x
        replace h2 : ∀ x : ℝ, x ≥ 0 → f x = x:= by
            intro x hx
            specialize h2 (√x)
            rw [show √x ^ 2 = x by exact Real.sq_sqrt hx] at h2
            exact h2
        -- For negative x,y, prove f(xf(y) - yf(x)) = 0
        have h3 : ∀ x y: ℝ, x < 0 → y < 0 → f (x * f y - y * f x) = 0:= by
            intro x y hx hy
            specialize h x y
            specialize h2 (x * y) (by exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
            rw [h2] at h
            simp at h
            exact h
        -- For negative x,y, prove xf(y) - yf(x) ≤ 0
        have h4 : ∀ x y : ℝ, x < 0 → y < 0 → x * f y - y * f x ≤ 0:= by
            intro x y hx hy
            by_contra H
            simp at H
            specialize h2 (x * f y - y * f x) (by linarith)
            specialize h3 x y hx hy
            linarith
        -- For negative x,y, prove xf(y) - yf(x) = 0
        have h5 : ∀ x y : ℝ, x < 0 → y < 0 → x * f y - y * f x = 0:= by
            intro x y hx hy
            have g1:= h4 x y hx hy
            have g2:= h4 y x hy hx
            linarith
        -- For negative x, prove f(x) = ax for some constant a
        replace h5 : ∃ a : ℝ, ∀ x : ℝ, x < 0 → f x = a * x:= by
            use (-f (-1))
            intro x hx
            specialize h5 x (-1) hx (by linarith)
            simp at h5
            linarith
        rcases h5 with ⟨a, h5⟩
        have g1:= h 1 (-1)
        have g2:= h (-1) 1
        ring_nf at g1 g2
        rw [h5 (-1) (by linarith)] at g1 g2
        rw [h2 1 (by linarith)] at g1 g2
        ring_nf at g1 g2
        by_cases ha : a = 1
        . -- If a = 1, then f(x) = x for all x
            subst a
            left
            intro x
            by_cases hx : x ≥ 0
            .
                specialize h2 x hx
                exact h2
            .
                simp at hx
                simp at h5
                specialize h5 x hx
                exact h5
        . -- If a ≠ 1, prove a = -1, which leads to f(x) = |x|
            replace ha : a < 1 ∨ a > 1:= by exact lt_or_gt_of_ne ha
            rcases ha with ha | ha
            .
                have g1:= h5 (-1 + a) (by linarith)
                rw [g1] at g2
                replace g2 : (a + 1) * (a - 1) = 0:= by linarith
                have g3 : a - 1 ≠ 0:= by
                    by_contra H
                    linarith
                replace g2 : a + 1 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero g3 g2
                replace g2 : a = -1:= by linarith
                subst a
                right
                intro x
                by_cases hx : x ≥ 0
                .
                    rw [show |x| = x by exact abs_of_nonneg hx]
                    specialize h2 x hx
                    exact h2
                .
                    simp at hx
                    rw [show |x| = -x by exact abs_of_neg hx]
                    simp at h5
                    specialize h5 x hx
                    exact h5
            .
                specialize h2 (-1 + a) (by linarith)
                rw [h2] at g2
                by_contra _
                linarith
    . -- Reverse direction: Prove both f(x) = x and f(x) = |x| satisfy the equation
        intro h
        rcases h with h | h
        . -- Case f(x) = x: Direct substitution
            simp [h]
            intro x y
            ring_nf
        . -- Case f(x) = |x|: Check different cases based on signs of x and y
            simp [h]
            intro x y
            by_cases hx : x ≥ 0
            .
                by_cases hy : y ≥ 0
                .
                    rw [show |x| = x by exact abs_of_nonneg hx]
                    rw [show |y| = y by exact abs_of_nonneg hy]
                    rw [show |x * y| = x * y by exact abs_of_nonneg (mul_nonneg hx hy)]
                    ring_nf
                    simp
                .
                    simp at hy
                    rw [show |x| = x by exact abs_of_nonneg hx]
                    rw [show |y| = -y by exact abs_of_neg (by linarith)]
                    ring_nf
                    replace hy : -y ≥ 0:= by linarith
                    have g1 : x * (-y) ≥ 0:= by positivity
                    replace g1 : x * y ≤ 0:= by linarith
                    rw [show |x * y| = -(x * y) by exact abs_of_nonpos g1]
                    simp
                    rw [show |x * y * 2| = -(x * y * 2) by exact abs_of_nonpos (by linarith)]
                    linarith
            .
                simp at hx
                replace hx : -x ≥ 0:= by linarith
                by_cases hy : y ≥ 0
                .
                    have g1 : (-x) * y ≥ 0:= by positivity
                    rw [show |x| = -x by exact abs_of_nonpos (by linarith)]
                    rw [show |y| = y by exact abs_of_nonneg hy]
                    ring_nf
                    rw [show |x * y * 2| = -(x * y * 2) by exact abs_of_nonpos (by linarith)]
                    rw [show |x * y| = -(x * y) by exact abs_of_nonpos (by linarith)]
                    ring_nf
                .
                    simp at hy
                    replace hy : -y ≥ 0:= by linarith
                    have g1 : (-x) * (-y) ≥ 0:= by positivity
                    rw [show |x| = -x by exact abs_of_nonpos (by linarith)]
                    rw [show |y| = -y by exact abs_of_nonpos (by linarith)]
                    rw [show |x * y| = x * y by exact abs_of_nonneg (by linarith)]
                    ring_nf
                    simp
