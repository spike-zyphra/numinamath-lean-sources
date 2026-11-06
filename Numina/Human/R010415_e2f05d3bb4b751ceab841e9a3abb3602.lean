import Mathlib
/- Déterminer toutes les fonctions f de $\mathbb{R}$ dans $\mathbb{R}$ telles que pour tous $x, y$ réels :

$$
f(x) f(y) f(x-y)=x^{2} f(y)-y^{2} f(x)
$$ -/
theorem algebra_607169 (f : ℝ → ℝ) : (∀ x y, f x * f y * f (x - y) = x ^ 2 * f y - y ^ 2 * f x) ↔ (∀ x, f x = 0) ∨ (∀ x, f x = x) ∨ (∀ x, f x = -x):= by
    constructor
    -- Forward direction: assuming the functional equation
    .
        intro h
        -- First prove f(0) = 0 by setting x = y = 0
        have h1 : f 0 = 0:= by
            specialize h 0 0
            simp at h
            exact h
        -- Case analysis: either f is identically 0
        by_cases h2 : ∀ x, f x = 0
        .
            left
            exact h2
        -- Or f is non-zero for some value
        .
            right
            simp at h2
            rcases h2 with ⟨a, h2⟩
            -- Prove that f(x) = 0 iff x = 0
            have h3 : ∀ x : ℝ, f x = 0 → x = 0:= by
                intro x hx
                specialize h x a
                rw [hx] at h
                simp at h
                simp [h2] at h
                exact h
            -- f is non-zero when x is non-zero
            replace h2 : ∀ x : ℝ, x ≠ 0 → f x ≠ 0:= by
                intro x hx
                by_contra H
                specialize h3 x H
                trivial
            clear h3 a
            -- Prove f is odd for differences
            have h3 : ∀ x y : ℝ, x ≠ 0 → y ≠ 0 → f (x - y) = -f (y - x):= by
                intro x y hx hy
                have g1:= h x y
                have g2:= h y x
                have g3 : f x * f y * (f (x - y) + f (y - x)) = 0:= by linarith
                have g4 : f x * f y ≠ 0:= by exact mul_ne_zero (h2 x hx) (h2 y hy)
                replace g3 : f (x - y) + f (y - x) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g4 g3
                linarith
            -- Prove f is odd everywhere
            replace h3 : ∀ x : ℝ, f (-x) = -f x:= by
                intro x
                by_cases hx : x = 0
                .
                    subst x
                    simp
                    rw [h1]
                    simp
                .
                    specialize h3 x (2 * x) hx (by positivity)
                    ring_nf at h3
                    exact h3
            -- Prove |f(x)| = |x| for all x
            have h4 : ∀ y : ℝ, f y ^ 2 = y ^ 2:= by
                intro y
                by_cases hy : y = 0
                .
                    subst y
                    simp
                    exact h1
                .
                    have g1:= h (2 * y) y
                    have g2:= h (-y) y
                    ring_nf at g1 g2
                    have g3:= h3 y
                    have g4:= h3 (y * 2)
                    rw [g3, g4] at g2
                    ring_nf at g2
                    rw [show f (y * 2) * f y ^ 2 = f y ^ 2 * f (y * 2) by ring] at g1
                    rw [g2] at g1
                    replace g1 : y ^ 2 * (f (y * 2) - 2 * f y) = 0:= by linarith
                    have hy1 : y ^ 2 ≠ 0:= by positivity
                    replace g1 : f (y * 2) - 2 * f y = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hy1 g1
                    ring_nf
                    replace g1 : f (y * 2) = 2 * f y:= by linarith
                    rw [g1] at g2
                    replace g2 : f y * (f y ^ 2 - y ^ 2) = 0:= by linarith
                    specialize h2 y hy
                    replace g2 : f y ^ 2 - y ^ 2 = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h2 g2
                    linarith
            -- Check if f(x) = x for all x
            by_cases h5 : ∀ x, f x = x
            .
                left
                exact h5
            -- If not, prove f(x) = -x for all x
            .
                right
                simp at h5
                rcases h5 with ⟨a, h5⟩
                have h6 : a ≠ 0:= by
                    by_contra H
                    rw [H] at h5
                    trivial
                replace h5 : f a = -a:= by
                    specialize h4 a
                    replace h4 : (f a - a) * (f a + a) = 0:= by linarith
                    replace h5 : f a - a ≠ 0:= by exact sub_ne_zero_of_ne h5
                    replace h4 : f a + a = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h5 h4
                    linarith
                by_contra H
                simp at H
                rcases H with ⟨b, H⟩
                have h7 : b ≠ 0:= by
                    by_contra H1
                    rw [H1, h1] at H
                    simp at H
                replace H : f b = b:= by
                    specialize h4 b
                    replace h4 : (f b + b) * (f b - b) = 0:= by linarith
                    replace H : f b + b ≠ 0:= by
                        by_contra H2
                        replace H2 : f b = -b:= by linarith
                        trivial
                    replace h4 : f b - b = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero H h4
                    linarith
                specialize h a b
                rw [h5, H] at h
                replace h : a * (b * (f (a - b) + a + b)) = 0:= by linarith
                replace h : b * (f (a - b) + a + b) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h6 h
                replace h : f (a - b) + a + b = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h7 h
                specialize h4 (a - b)
                replace h4 : (f (a - b) - a + b) * (f (a - b) + a - b) = 0:= by linarith
                replace h4 : f (a - b) - a + b = 0 ∨ f (a - b) + a - b = 0:= by exact mul_eq_zero.mp h4
                rcases h4 with h4 | h4
                .
                    have h8 : a = 0:= by linarith
                    trivial
                .
                    have h8 : b = 0:= by linarith
                    trivial
    -- Backward direction: proving each case satisfies the equation
    .
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
