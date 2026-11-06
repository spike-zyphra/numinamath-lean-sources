import Mathlib
/- Déterminer toutes les fonctions $f: \mathbb{R} \rightarrow \mathbb{R}$ telles que pour tous $x, y$ réels, on ait

$$
f\left(x^{2}+x y+f\left(y^{2}\right)\right)=x f(y)+f\left(x^{2}\right)+y^{2}
$$ -/
theorem algebra_607171 (f : ℝ → ℝ) : (∀ x y, f (x ^ 2 + x * y + f (y ^ 2)) = x * f y + f (x ^ 2) + y ^ 2) ↔
(∀ x, f x = x) ∨ (∀ x, f x = -x):= by
    constructor
    .
        intro h
        -- First prove that f(0) = 0 using x = 1 and x = -1 with y = 0
        have h1 : f 0 = 0:= by
            have g1:= h 1 0
            have g2:= h (-1) 0
            simp at g1 g2
            linarith
        -- Prove that f(y²) = y * f(y) for all real y
        have h2 : ∀ y : ℝ, f (y ^ 2) = y * f y:= by
            intro y
            have g1:= h 0 y
            have g2:= h (-y) y
            ring_nf at g1 g2
            linarith
        -- For any non-zero y, prove that f(y) = y or f(y) = -y
        have h3 : ∀ y : ℝ, y ≠ 0 → f y = y ∨ f y = -y:= by
            intro y hy
            have g1:= h (-f (y ^ 2) / y) y
            field_simp at g1
            apply sub_eq_zero.2 at g1
            ring_nf at g1
            field_simp at g1
            rw [show y * f (y ^ 2) ^ 2 / y ^ 3 = f (y ^ 2) ^ 2 / y ^ 2 by field_simp ; linarith] at g1
            ring_nf at g1
            rw [h2 y] at g1
            replace g1 : y * (f y - y) * (f y + y) = 0:= by linarith
            simp [hy] at g1
            rcases g1 with g1 | g1
            .
                left
                linarith
            .
                right
                linarith
        -- Extend the previous result to include y = 0
        replace h3 : ∀ y : ℝ, f y = y ∨ f y = -y:= by
            intro y
            by_cases hy : y = 0
            .
                subst y
                rw [h1]
                simp
            .
                specialize h3 y hy
                exact h3
        -- Check if there exists a non-zero b where f(b) = -b
        by_cases h4 : ∃ b : ℝ, b ≠ 0 ∧ f b = -b
        .
            rcases h4 with ⟨b, hbne, hb⟩
            -- Check if there exists a non-zero a where f(a) = a
            by_cases h5 : ∃ a : ℝ, a ≠ 0 ∧ f a = a
            .
                rcases h5 with ⟨a, hane, ha⟩
                have g1:= h2 a
                rw [ha] at g1
                have g2:= h2 b
                rw [hb] at g2
                ring_nf at g1 g2
                have g3:= h a b
                rw [g1, g2, hb] at g3
                specialize h3 (a ^ 2 + a * b + -b ^ 2)
                rcases h3 with h3 | h3
                .
                    replace h3 : b * (a - b) = 0:= by linarith
                    simp [hbne] at h3
                    replace h3 : a = b:= by linarith
                    subst a
                    replace hb : b = 0:= by linarith
                    by_contra _
                    trivial
                .
                    replace h3 : a ^ 2 = 0:= by linarith
                    simp at h3
                    by_contra _
                    trivial
            .
                simp at h5
                right
                intro x
                by_cases hx : x = 0
                .
                    subst x
                    linarith
                .
                    specialize h5 x hx
                    specialize h3 x
                    simp [h5] at h3
                    exact h3
        .
            simp at h4
            left
            intro x
            by_cases hx : x = 0
            .
                subst x
                exact h1
            .
                specialize h4 x hx
                specialize h3 x
                simp [h4] at h3
                exact h3
    .
        intro h
        rcases h with h | h
        all_goals
            simp [h]
            intro x y
            linarith
