import Mathlib
/- Denote by $\mathbb{R}^{+}$the set of all positive real numbers. Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$such that  $$ x f\left(x^{2}\right) f(f(y))+f(y f(x))=f(x y)\left(f\left(f\left(x^{2}\right)\right)+f\left(f\left(y^{2}\right)\right)\right) $$  for all positive real numbers $x$ and $y$. -/
theorem algebra_24739 {f : ℝ → ℝ} (hf : ∀ x > 0, f x > 0) :
(∀ x y, x > 0 → y > 0 → x * f (x ^ 2) * f (f y) + f (y * f x) = f (x * y) * (f (f (x ^ 2)) + f (f (y ^ 2)))) ↔ ∀ y, 0 < y → f y = 1 / y := by
    constructor
    .
        intro h
        -- Prove that f(1) = 1
        have h1 : f 1 = 1:= by
            specialize h 1 1 (by linarith) (by linarith)
            simp at h
            replace h : (f 1 - 1) * (f (f 1)) = 0:= by linarith
            simp at h
            specialize hf (f 1) (hf 1 (by linarith))
            replace hf : f (f 1) ≠ 0:= by linarith
            simp [hf] at h
            linarith
        -- Prove that f(f(y)) = f(y) * f(f(y^2)) for all positive y
        have h2 : ∀ y : ℝ, y > 0 → f (f y) = (f y) * f (f (y ^ 2)):= by
            intro y hy
            specialize h 1 y (by linarith) hy
            simp at h
            rw [h1] at h
            rw [h1] at h
            simp at h
            linarith
        -- Prove that x * f(x^2) = f(x) for all positive x
        have h3 : ∀ x : ℝ, x > 0 → x * f (x ^ 2) = f x:= by
            intro x hx
            specialize h x 1 hx (by linarith)
            simp at h
            specialize h2 x hx
            rw [h1] at h
            rw [h1] at h
            linarith
        -- Prove that f(x) * f(1/x) = 1 for all positive x
        have h4 : ∀ x : ℝ, x > 0 → (f x) * (f (1 / x)) = 1:= by
            intro x hx
            specialize h x (1 / x) hx (by positivity)
            field_simp at h
            specialize h3 x hx
            replace h3 : f (x ^ 2) = f x / x:= by
                field_simp
                linarith
            rw [h1, h3] at h
            field_simp at h
            specialize h2 (1 / x) (by positivity)
            rw [h2] at h
            field_simp at h
            replace h : ((f x) * (f (1 / x)) - 1) * (f (f (1 / x ^ 2))) = 0:= by linarith
            simp at h
            specialize hf (f (1 / x ^ 2)) (hf (1 / x ^ 2) (by positivity))
            replace hf : f (f (1 / x ^ 2)) ≠ 0:= by linarith
            simp at hf
            simp [hf] at h
            field_simp at h
            linarith
        -- Complex equality involving squares of function values
        have h5 : ∀ x y : ℝ, x > 0 → y > 0 → (f (x * y)) ^ 2 * (f (f (x ^ 2))) * (f (f (y ^ 2))) = x * (f (x ^ 2)) * (f (f y)) * f (y * (f x)):= by
            intro x y hx hy
            have g0:= h x y (by positivity) (by positivity)
            specialize h (1 / x) (1 / y) (by positivity) (by positivity)
            field_simp at h
            replace h4 : ∀ x : ℝ, x > 0 → f (1 / x) = 1 / f x:= by
                intro x hx
                specialize hf x hx
                field_simp
                specialize h4 x hx
                linarith
            rw [h4 y hy, h4 (x * y) (by positivity), h4 x hx, h4 (x ^ 2) (by positivity), h4 (y ^ 2) (by positivity)] at h
            field_simp at h
            rw [h4 (f y) (hf y (by positivity)), h4 (f x * y) (by specialize hf x hx ; positivity), h4 (f (x ^ 2)) (hf (x ^ 2) (by positivity)), h4 (f (y ^ 2)) (hf (y ^ 2) (by positivity))] at h
            field_simp at h
            have g1:= hf (f y) (hf y (by positivity))
            have g2:= hf (f x * y) (by specialize hf x hx ; positivity)
            have g3:= hf (f (x ^ 2)) (hf (x ^ 2) (by positivity))
            have g4:= hf (f (y ^ 2)) (hf (y ^ 2) (by positivity))
            have g5:= hf (x * y) (by positivity)
            have g6:= hf (x ^ 2) (by positivity)
            field_simp at h
            rw [show f x * y = y * f x by ring] at h
            rw [show f (y * f x) + x * (f (f y) * f (x ^ 2)) = x * f (x ^ 2) * f (f y) + f (y * f x) by ring] at h
            rw [g0] at h
            replace h : (f (f (x ^ 2)) + f (f (y ^ 2))) * ((f (x * y)) ^ 2 * (f (f (x ^ 2))) * (f (f (y ^ 2))) - x * (f (x ^ 2)) * (f (f y)) * f (y * (f x))) = 0:= by linarith
            have g7 : f (f (x ^ 2)) + f (f (y ^ 2)) ≠ 0:= by positivity
            simp [g7] at h
            linarith
        replace h5 : ∀ x y : ℝ, x > 0 → y > 0 → (f (x * y)) ^ 2 * (f (f x)) = (f x) ^ 2 * (f y) * (f (y * (f x))):= by
            intro x y hx hy
            specialize h5 x y hx hy
            rw [h3 x hx] at h5
            replace h5 : (f x) * (f (x * y) ^ 2 * f (f (x ^ 2)) * f (f (y ^ 2))) = (f x) * (f x * f (f y) * f (y * f x)):= by rw [h5]
            rw [show (f x) * (f (x * y) ^ 2 * f (f (x ^ 2)) * f (f (y ^ 2))) = f (x * y) ^ 2 * ((f x) * (f (f (x ^ 2)))) * (f (f (y ^ 2))) by ring] at h5
            rw [←h2 x hx] at h5
            rw [h2 y hy] at h5
            replace h5 : (f (f (y ^ 2))) * (f (x * y) ^ 2 * f (f x) - (f x ^ 2 * f y * f (y * f x))) = 0:= by linarith
            have g1:= hf (f (y ^ 2)) (hf (y ^ 2) (by positivity))
            replace g1 : f (f (y ^ 2)) ≠ 0:= by linarith
            simp [g1] at h5
            linarith
        -- Simplified version of h5 relating function values
        have h6 : ∀ x : ℝ, x > 0 → f (x * (f x)) ^ 2 = (f x) * (f (f x)):= by
            intro x hx
            specialize h5 x (f x) hx (hf x (by positivity))
            rw [show f x * f x = f x ^ 2 by ring] at h5
            rw [←h3 (f x) (hf x (by positivity))] at h5
            replace h5 : f x * f (f x ^ 2) * (f (x * (f x)) ^ 2 - (f x) * (f (f x))) = 0:= by rw [←h3 (f x) (hf x (by positivity))] ; linarith
            have g1:= hf x hx
            have g2 : f x ^ 2 > 0:= by
                specialize hf x hx
                positivity
            replace g2:= hf (f x ^ 2) g2
            have g3 : f x * (f (f x ^ 2)) ≠ 0:= by positivity
            simp [g3] at h5
            linarith
        -- Key relationship: f(f(x)) = x^4 * f(x)^3
        have h7 : ∀ x : ℝ, x > 0 → f (f x) = x ^ 4 * (f x) ^ 3:= by
            intro x hx
            specialize h6 x hx
            specialize h5 x x hx hx
            replace h5 : (f (x * x) ^ 2 * f (f x)) ^ 2 = (f x ^ 2 * f x * f (x * f x)) ^ 2:= by rw [h5]
            rw [show (f x ^ 2 * f x * f (x * f x)) ^ 2 = (f x ^ 2 * f x) ^ 2 * (f (x * f x)) ^ 2 by ring] at h5
            rw [h6] at h5
            ring_nf at h5
            replace h5 : x ^ 4 * (f (x ^ 2) ^ 4 * f (f x) ^ 2) = x ^ 4 * (f (f x) * f x ^ 7):= by rw [h5]
            rw [show x ^ 4 * (f (x ^ 2) ^ 4 * f (f x) ^ 2) = (x * f (x ^ 2)) ^ 4 * f (f x) ^ 2 by ring] at h5
            rw [h3 x hx] at h5
            ring_nf at h5
            replace h5 : f x ^ 4 * f (f x) * (f (f x) - x ^ 4 * f x ^ 3) = 0:= by linarith
            have g1:= hf x hx
            have g2:= hf (f x) (hf x (by positivity))
            have g3 : f x ^ 4 * f (f x) ≠ 0:= by positivity
            simp [g3] at h5
            linarith
        -- Final step to prove f(x) = 1/x
        intro x hx
        have h8:= h7 x hx
        rw [h2 x hx] at h8
        rw [h7 (x ^ 2) (by positivity)] at h8
        ring_nf at h8
        rw [show f x * x ^ 8 * f (x ^ 2) ^ 3 = f x * x ^ 5 * (x * f (x ^ 2)) ^ 3 by ring] at h8
        rw [h3 x hx] at h8
        ring_nf at h8
        replace h8 : f x ^ 3 * x ^ 4 * (x * f x - 1) = 0:= by linarith
        have g1:= hf x hx
        have g2 : f x ^ 3 * x ^ 4 ≠ 0:= by positivity
        simp [g2] at h8
        field_simp
        linarith
    -- Prove the reverse implication: if f(y) = 1/y, then the functional equation holds
    .
        intro h
        intro x y hx hy
        rw [h (f (x ^ 2)) (hf (x ^ 2) (by positivity))]
        rw [h (f (y ^ 2)) (hf (y ^ 2) (by positivity))]
        rw [h (y * f x) (by specialize hf x hx ; positivity)]
        rw [h (f y) (hf y (by positivity))]
        rw [h (x ^ 2) (by positivity)]
        rw [h (y ^ 2) (by positivity)]
        rw [h x hx, h y hy, h (x * y) (by positivity)]
        field_simp
        linarith
