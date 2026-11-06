import Mathlib
/- Find all real-valued functions $f$ defined on the set of all non-zero real numbers such that:

(i) $f(1)=1$,

(ii) $f\left(\frac{1}{x+y}\right)=f\left(\frac{1}{x}\right)+f\left(\frac{1}{y}\right)$ for all non-zero $x, y, x+y$,

(iii) $(x+y) f(x+y)=x y f(x) f(y)$ for all non-zero $x, y, x+y$. -/
theorem algebra_241567 {f : ℝ → ℝ} : (f 1 = 1 ∧ (∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → f (1 / (x + y)) = f (1 / x) + f (1 / y)) ∧ (∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → (x + y) * f (x + y) = x * y * f x * f y)) ↔ ∀ x, x ≠ 0 → f x = 1 / x:= by
    constructor
    .
        intro h
        rcases h with ⟨h1, h2, h3⟩
        -- Prove that f(1/z) = 2*f(2/z) for any non-zero z
        have h4 : ∀ z : ℝ, z ≠ 0 → f (1 / z) = 2 * f (2 / z):= by
            intro z hz
            -- Prove z/2 ≠ 0
            have g0 : z / 2 ≠ 0:= by
                by_contra H
                simp at H
                trivial
            -- Prove z/2 + z/2 ≠ 0
            have g1 : z / 2 + z / 2 ≠ 0:= by
                by_contra H
                simp at H
                trivial
            specialize h2 (z / 2) (z / 2) g0 g0 g1
            ring_nf at h2
            ring_nf
            exact h2
        -- Prove relationship between f(2/z) and f(1/z)
        have h5 : ∀ z : ℝ, z ≠ 0 → 2 / z * f (2 / z) = 1 / z ^ 2 * (f (1 / z)) ^ 2:= by
            intro z hz
            -- Prove 1/z ≠ 0
            have g0 : 1 / z ≠ 0:= by
                by_contra H
                simp at H
                trivial
            -- Prove 1/z + 1/z ≠ 0
            have g1 : 1 / z + 1 / z ≠ 0:= by
                by_contra H
                simp at H
                trivial
            specialize h3 (1 / z) (1 / z) g0 g0 g1
            ring_nf at h3
            ring_nf
            exact h3
        -- Simplify to show f(1/z) = 1/z * (f(1/z))^2
        replace h5 : ∀ z : ℝ, z ≠ 0 → f (1 / z) = 1 / z * (f (1 / z)) ^ 2:= by
            intro z hz
            specialize h4 z hz
            specialize h5 z hz
            field_simp at h5
            rw [←h4] at h5
            field_simp
            replace h5 : z * (z * f (1 / z) - f (1 / z) ^ 2) = 0:= by linarith
            simp [hz] at h5
            simp
            linarith
        -- Show that f(x) = x * (f(x))^2 for all non-zero x
        replace h5 : ∀ x : ℝ, x ≠ 0 → f x = x * (f x) ^ 2:= by
            intro x hx
            have g0 : 1 / x ≠ 0:= by
                by_contra H
                simp at H
                trivial
            specialize h5 (1 / x) g0
            field_simp at h5
            exact h5
        -- Case analysis on whether f is never zero
        by_cases h6 : ∀ x : ℝ, x ≠ 0 → f x ≠ 0
        .
            -- If f is never zero, prove f(x) = 1/x
            intro x hx
            specialize h6 x hx
            specialize h5 x hx
            replace h5 : f x * (f x * x - 1) = 0:= by linarith
            simp [h6] at h5
            field_simp
            linarith
        .
            -- If f is zero somewhere, derive a contradiction
            simp at h6
            rcases h6 with ⟨a, ha, hf⟩
            by_contra _
            have h6 : 1 - a ≠ 0:= by
                by_contra H
                replace H : a = 1:= by linarith
                subst a
                linarith
            specialize h3 a (1 - a) ha h6 (by simp)
            ring_nf at h3
            rw [hf] at h3
            simp at h3
            linarith
    .
        -- Prove the reverse direction
        intro h
        refine ⟨?_, ?_, ?_⟩
        .
            -- Verify f(1) = 1
            specialize h 1 (by simp)
            simp at h
            exact h
        .
            -- Verify condition (ii)
            intro x y hx hy hxy
            have h1 : 1 / x ≠ 0:= by
                by_contra H
                simp at H
                trivial
            have h2 : 1 / y ≠ 0:= by
                by_contra H
                simp at H
                trivial
            have h3 : 1 / (x + y) ≠ 0:= by
                by_contra H
                simp at H
                trivial
            rw [h (1 / x) h1, h (1 / y) h2, h (1 / (x + y)) h3]
            field_simp
        .
            -- Verify condition (iii)
            intro x y hx hy hxy
            rw [h x hx, h y hy, h (x + y) hxy]
            field_simp
