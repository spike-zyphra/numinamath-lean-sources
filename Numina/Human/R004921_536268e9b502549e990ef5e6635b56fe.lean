import Mathlib
/- Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ waarvoor geldt dat

$$
x f(x+x y)=x f(x)+f\left(x^{2}\right) f(y)
$$

voor alle $x, y \in \mathbb{R}$. -/
theorem algebra_604643 (f : ℝ → ℝ) : (∀ x y, x * f (x + x * y) = x * f x + f (x ^ 2) * f y) ↔
    (∀ x, f x = 0) ∨ (∀ x, f x = x):= by
        constructor
        . -- Forward direction: proving that f must be either constantly 0 or f(x) = x
            intro h
            -- First prove f(0) = 0 by setting x = y = 0
            have h1 : f 0 = 0:= by
                specialize h 0 0
                simp at h
                exact h
            -- Next prove that either f(1) = 0 or f(-1) = -1 by setting x = 1, y = -1
            have h2 : f 1 = 0 ∨ f (-1) = -1:= by
                specialize h 1 (-1)
                simp at h
                rw [h1] at h
                replace h : f 1 * (f (-1) + 1) = 0:= by linarith
                replace h : f 1 = 0 ∨ f (-1) + 1 = 0:= by exact mul_eq_zero.mp h
                rcases h with h | h
                .
                    left
                    exact h
                .
                    right
                    linarith
            rcases h2 with h2 | h2
            . -- Case 1: If f(1) = 0, prove f is constantly 0
                -- Show that f(-1 + -y) = f(-1) for all y
                have h3 : ∀ y : ℝ, f (-1 + -y) = f (-1):= by
                    intro y
                    specialize h (-1) y
                    simp at h
                    rw [h2] at h
                    simp at h
                    exact h
                -- Prove f(-1) = 0
                have h4 : f (-1) = 0:= by
                    specialize h3 (-1)
                    simp at h3
                    linarith
                rw [h4] at h3
                left
                intro x
                specialize h3 (-x - 1)
                simp at h3
                exact h3
            . -- Case 2: If f(-1) = -1, prove f(x) = x for all x
                -- First prove f(1) = 1
                have h3 : f 1 = 1:= by
                    specialize h (-1) (-1)
                    simp at h
                    rw [h2] at h
                    linarith
                -- Show that f(1 + y) = f(y) + 1 for all y
                have h4 : ∀ y : ℝ, f (1 + y) = f y + 1:= by
                    intro y
                    specialize h 1 y
                    simp at h
                    rw [h3] at h
                    linarith
                -- Prove that x * f(x) = f(x²) for all x
                have h5 : ∀ x : ℝ, x * f x = f (x ^ 2):= by
                    intro x
                    specialize h x (-1)
                    simp at h
                    rw [h1, h2] at h
                    simp at h
                    linarith
                -- For x ≠ 0, prove f(x + xy) = f(x) * f(y + 1)
                have h6 : ∀ x y : ℝ, x ≠ 0 → f (x + x * y) = f x * f (y + 1):= by
                    intro x y hx
                    specialize h x y
                    specialize h5 x
                    rw [←h5] at h
                    rw [show x * f x + x * f x * f y = x * f x * (f y + 1) by ring] at h
                    specialize h4 y
                    rw [show 1 + y = y + 1 by ring] at h4
                    rw [←h4] at h
                    replace h : x * (f (x + x * y) - f x * f (y + 1)) = 0:= by linarith
                    replace h : f (x + x * y) - f x * f (y + 1) = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero hx h
                    linarith only [h]
                -- Prove multiplicativity: f(x*z) = f(x)*f(z)
                have h7 : ∀ x z : ℝ, f (x * z) = f x * f z:= by
                    intro x z
                    by_cases hx : x = 0
                    .
                        subst x
                        simp
                        rw [h1]
                        simp
                    .
                        specialize h6 x (z - 1) hx
                        ring_nf at h6
                        exact h6
                -- Prove f(x) ≠ 0 when x ≠ 0
                have h8 : ∀ x : ℝ, x ≠ 0 → f x ≠ 0:= by
                    by_contra H
                    simp at H
                    rcases H with ⟨x, hx, H⟩
                    specialize h7 x (1 / x)
                    rw [show x * (1 / x) = 1 by field_simp] at h7
                    rw [H] at h7
                    simp at h7
                    linarith
                -- Finally prove f(x) = x for all x
                right
                intro x
                by_cases hx : x = 0
                .
                    subst x
                    exact h1
                .
                    specialize h8 x hx
                    specialize h7 x x
                    ring_nf at h7
                    specialize h5 x
                    rw [←h5] at h7
                    replace h7 : f x * (f x - x) = 0:= by linarith
                    replace h7 : f x - x = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero h8 h7
                    linarith
        . -- Backward direction: proving both cases satisfy the functional equation
            intro h
            rcases h with h | h
            . -- Case f(x) = 0
                simp [h]
            . -- Case f(x) = x
                simp [h]
                intro x y
                linarith
