import Mathlib
/- Determine all functions $f$ defined on the set of rationals that take rational values for which

$$
f(2 f(x)+f(y))=2 x+y
$$

for each $x$ and $y$. -/

theorem algebra_605314 {f : ℚ → ℚ} : (∀ x y, f (2 * f x + f y) = 2 * x + y) ↔ ((∀ x, f x = x) ∨ (∀ x, f x = -x)):= by
    constructor
    .
        intro h
        -- For all x, f(3f(x)) = 3x
        have h1 : ∀ x : ℚ, f (3 * f x) = 3 * x:= by
            intro x
            specialize h x x
            ring_nf at h
            ring_nf
            exact h
        -- For all x, f(9x) = 9f(x)
        have h2 : ∀ x : ℚ, f (9 * x) = 9 * f x:= by
            intro x
            have g1:= h1 x
            have g2:= h1 (3 * f x)
            rw [g1] at g2
            ring_nf at g2
            ring_nf
            exact g2
        -- f(0) = 0
        have h3 : f 0 = 0:= by
            specialize h2 0
            simp at h2
            linarith
        -- For all y, f(f(y)) = y (f is an involution)
        have h4 : ∀ y : ℚ, f (f y) = y:= by
            intro y
            specialize h 0 y
            rw [h3] at h
            simp at h
            exact h
        -- For all x and y, 2f(x) + f(y) = f(2x + y)
        have h5 : ∀ x y : ℚ, 2 * f x + f y = f (2 * x + y):= by
            intro x y
            specialize h x y
            have g1:= h4 (2 * f x + f y)
            rw [h] at g1
            rw [g1]
        -- For all x, f(2x) = 2f(x) (f is homogeneous for 2)
        have h6 : ∀ x : ℚ, f (2 * x) = 2 * f x:= by
            intro x
            specialize h5 x 0
            rw [h3] at h5
            simp at h5
            rw [h5]
        -- For all x and y, f(x + y) = f(x) + f(y) (f is additive)
        have h7 : ∀ x y : ℚ, f x + f y = f (x + y):= by
            intro x y
            specialize h6 (x / 2)
            specialize h5 (x / 2) y
            rw [←h6] at h5
            ring_nf at h5
            rw [h5]
        -- For all natural numbers n and rationals x, f(nx) = nf(x)
        have h8 : ∀ n : ℕ, ∀ x : ℚ, f (n * x) = n * f x:= by
            intro n
            induction n with
            | zero =>
                intro x
                simp
                rw [h3]
            | succ n hn =>
                intro x
                field_simp
                specialize hn x
                specialize h7 (n * x) x
                rw [show (n + 1) * x = n * x + x by ring_nf]
                rw [←h7, hn]
                linarith
        -- For positive x, f(x) = x * f(1)
        have h9 : ∀ x : ℚ, x > 0 → f x = x * f 1:= by
            intro x hx
            have g1 : x = (x.num) / (x.den):= by exact Eq.symm (Rat.num_div_den x)
            set a:= (x.num).natAbs with ha
            set b:= x.den with hb
            clear_value a b
            have _ : x.num > 0:= by
                by_contra H
                simp at H
                linarith
            replace hapos : x = a / b:= by
                rw [ha, hb]
                have g2 : (↑x.num.natAbs : ℚ) = ↑x.num:= by
                    rw [show (↑x.num.natAbs : ℚ) = (↑(↑x.num.natAbs : ℤ) : ℚ) by rfl]
                    simp
                    linarith
                rw [g2, ←hb, ←g1]
            replace hb : b > 0:= by
                rw [hb]
                exact Rat.den_pos x
            replace _ : a > 0:= by
                rw [ha]
                simp
                positivity
            have g2:= h8 a (1 / ↑b)
            have g3:= h8 b (1 / ↑b)
            rw [show ↑a * (1 / (↑b : ℚ)) = (↑a : ℚ) / (↑b : ℚ) by ring_nf] at g2
            rw [show ↑b * (1 / (↑b : ℚ)) = 1 by field_simp] at g3
            replace g3 : f (1 / ↑b) = 1 / ↑b * f 1:= by
                field_simp
                linarith
            rw [hapos, g2, g3]
            field_simp
        -- Extend the previous result to all x: f(x) = x * f(1)
        replace h9 : ∀ x : ℚ, f x = x * f 1:= by
            intro x
            by_cases hx : x > 0
            .
                specialize h9 x hx
                exact h9
            .
                simp at hx
                by_cases hxne : x = 0
                .
                    subst x
                    simp
                    rw [h3]
                .
                    replace hx : x < 0:= by
                        by_contra H
                        simp at H
                        replace H : x = 0:= by linarith
                        trivial
                    specialize h7 x (-x)
                    specialize h9 (-x) (by linarith)
                    rw [h9] at h7
                    ring_nf at h7
                    rw [h3] at h7
                    linarith
        -- Prove that f(1) must be either 1 or -1
        have h10 : f 1 = 1 ∨ f 1 = -1:= by
            specialize h 1 1
            specialize h9 (2 * f 1 + f 1)
            rw [h9] at h
            ring_nf at h
            replace h : (f 1 - 1) * (f 1 + 1) = 0:= by linarith
            replace h : f 1 - 1 = 0 ∨ f 1 + 1 = 0:= by exact mul_eq_zero.mp h
            rcases h with h | h
            .
                left
                linarith
            .
                right
                linarith
        rcases h10 with h10 | h10
        all_goals
        rw [h10] at h9
        simp at h9
        simp [h9]
    .
        -- Prove the reverse direction: if f is identity or negation, then it satisfies the original equation
        intro h
        rcases h with h | h
        .
            simp [h]
        .
            simp [h]
            intro x y
            linarith
