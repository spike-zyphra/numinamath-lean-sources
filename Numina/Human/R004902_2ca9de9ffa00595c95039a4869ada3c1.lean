import Mathlib
/- Determine all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ satisfying the condition

$$
f\left(y^{2}+2 x f(y)+f(x)^{2}\right)=(y+f(x))(x+f(y))
$$

for all real numbers $x$ and $y$.
Proposed by Daniël Kroes, NLD
The answer is the functions $f(x)=x, f(x)=-x$ and $f(x)=\frac{1}{2}-x$. -/
theorem algebra_604525 (f : ℝ → ℝ) : (∀ x y : ℝ, f (y ^ 2 + 2 * x * f y + (f x) ^ 2) = (y + f x) * (x + f y)) ↔
(∀ x, f x = x) ∨ (∀ x, f x = -x) ∨ (∀ x, f x = 1 / 2 - x):= by
    constructor
    .
        intro h
        -- Lemma 1: For all x, f(2f(x)² + 2xf(-f(x))) = 0
        have h1 : ∀ x : ℝ, f (2 * (f x) ^ 2 + 2 * x * f (-f x)) = 0:= by
            intro x
            specialize h x (-f x)
            ring_nf
            ring_nf at h
            exact h
        -- Lemma 2: If f(u) = f(v) = 0, then u = v
        -- This shows f⁻¹(0) contains at most one element
        have h2 : ∀ u v : ℝ, f u = 0 → f v = 0 → u = v:= by
            intro u v hu hv
            have g1:= h u u
            have g2:= h v v
            have g3:= h u v
            have g4:= h v u
            rw [hu] at g1 g4
            rw [hv] at g2 g3
            ring_nf at g1 g2 g3 g4
            rw [hu] at g3
            rw [hv] at g4
            ring_nf at g3 g4
            have g5 : (u + v) * (u - v) = 0:= by linarith
            simp at g5
            rcases g5 with g5 | g5
            .
                replace g5 : u = -v:= by linarith
                have g6 : u * (u - v) = 0:= by linarith
                simp at g6
                rcases g6 with g6 | g6
                .
                    subst u
                    simp at g6
                    subst v
                    simp
                .
                    linarith
            .
                linarith
        -- Lemma 3: There exists a value 'a' such that:
        -- 1. f(a) = 0
        -- 2. a = 2f(0)²
        -- 3. For all x, 2f(x)² + 2xf(-f(x)) = a
        have h3 : ∃ a : ℝ, f a = 0 ∧ a = f 0 ^ 2 * 2 ∧ ∀ x : ℝ, 2 * f x ^ 2 + 2 * x * f (-f x) = a:= by
            have g1:= h1 0
            ring_nf at g1
            use (f 0 ^ 2 * 2)
            simp [g1]
            intro x
            specialize h1 x
            specialize h2 (f 0 ^ 2 * 2) (2 * f x ^ 2 + 2 * x * f (-f x)) g1 (by linarith)
            rw [h2]
        rcases h3 with ⟨a, ha, haeq, h3⟩
        -- Lemma 4: If f(x) = f(y), then x = y or x = -y
        -- This shows f is at most 2-to-1
        have h4 : ∀ x y : ℝ, f x = f y → x = y ∨ x = -y:= by
            intro x y hxy
            have g1:= h3 x
            have g2:= h3 y
            have g3 : f x ^ 2 = f y ^ 2:= by rw [hxy]
            replace g1 : x * f (-f x) = y * f (-f y):= by linarith
            rw [hxy] at g1
            clear g2 g3
            replace g1 : (x - y) * f (-f y) = 0:= by linarith
            simp at g1
            rcases g1 with g1 | g1
            .
                left
                linarith
            .
                have g2:= h2 a (-f y) ha g1
                replace g2 : f y = -a:= by linarith
                rw [g2] at hxy
                have g3:= h a x
                have g4:= h a y
                rw [hxy, ha] at g3
                rw [g2, ha] at g4
                ring_nf at g3 g4
                have g5:= h2 a (x ^ 2 - a ^ 2 * 2) ha g3
                have g6:= h2 a (-(a ^ 2 * 2) + y ^ 2) ha g4
                have g7 : (x - y) * (x + y) = 0:= by linarith
                simp at g7
                rcases g7 with g7 | g7
                .
                    left
                    linarith
                .
                    right
                    linarith
        -- Lemma 5: The expression y² + 2xf(y) + f(x)² is symmetric in x and y
        have h5 : ∀ x y : ℝ, y ^ 2 + 2 * x * f y + f x ^ 2 = x ^ 2 + 2 * y * f x + f y ^ 2:= by
            intro x y
            have g1:= h x y
            have g2:= h y x
            by_cases hx : (x + f y) * (y + f x) = 0
            .
                exact h2 _ _ (by linarith) (by linarith)
            .
                specialize h4 (x ^ 2 + 2 * y * f x + f y ^ 2) (y ^ 2 + 2 * x * f y + f x ^ 2) (by linarith)
                simp at h4
                rcases h4 with h4 | h4
                .
                    linarith
                .
                    replace h4 : (f x + y) ^ 2 + (f y + x) ^ 2 = 0:= by linarith
                    have g1 : (f x + y) ^ 2 ≥ 0:= by positivity
                    have g2 : (f y + x) ^ 2 ≥ 0:= by positivity
                    replace g1 : (f x + y) ^ 2 = 0:= by linarith
                    replace g2 : (f y + x) ^ 2 = 0:= by linarith
                    simp at g1 g2
                    replace g1 : x + f y = 0:= by linarith
                    rw [g1] at hx
                    by_contra _
                    simp at hx
        -- Lemma 6: For all x, f(x)² = (f(0) - x)²
        have h6 : ∀ x : ℝ, f x ^ 2 = (f 0 - x) ^ 2:= by
            intro x
            specialize h5 x 0
            linarith
        -- Main case analysis: Check if f(0) = 0
        by_cases h7 : f 0 = 0
        .
            -- Case 1: When f(0) = 0
            -- Using h6 (which states f(x)² = (f(0) - x)²) and evaluating at x = 1
            rw [h7] at h6
            simp at h6
            have g1:= h6 1
            simp at g1
            rcases g1 with g1 | g1
            .
                -- Subcase 1a: Proves f(x) = x
                left
                intro x
                specialize h6 x
                specialize h5 1 x
                rw [h6, g1] at h5
                ring_nf at h5
                linarith
            .
                -- Subcase 1b: Proves f(x) = -x
                right
                left
                intro x
                specialize h6 x
                specialize h5 1 x
                rw [h6, g1] at h5
                simp at h5
                linarith
        .
            -- Case 2: When f(0) ≠ 0
            -- From h6, we know that for all x, f(x) = x - f(0) or f(x) = -x + f(0)
            simp at h6
            replace h6 : ∀ x : ℝ, f x = x - f 0 ∨ f x = -x + f 0:= by
                intro x
                specialize h6 x
                replace h6 : (f x - f 0 + x) * (f x + f 0 - x) = 0:= by linarith
                simp at h6
                rcases h6 with h6 | h6
                .
                    right
                    linarith
                .
                    left
                    linarith
            clear h1 h3 h4
            -- Check if f(x) = x - f(0) holds for all nonzero x
            by_cases h8 : ∀ x : ℝ, x ≠ 0 → f x = x - f 0
            .
                -- This case leads to a contradiction as it implies f(0) = 0
                have g1:= h8 1 (by simp)
                have g2:= h8 (-1) (by simp)
                specialize h5 1 (-1)
                rw [g1, g2] at h5
                ring_nf at h5
                replace h5 : f 0 = 0:= by linarith
                by_contra _
                trivial
            .
                -- There exists some b where f(b) = -b + f(0)
                simp at h8
                rcases h8 with ⟨b, hbne, hb⟩
                replace hb : f b = -b + f 0:= by
                    specialize h6 b
                    simp [hb] at h6
                    exact h6
                -- Check if f(x) = -x + f(0) holds for all x
                by_cases h9 : ∀ x : ℝ, f x = -x + f 0
                .
                    -- This case proves f(x) = 1/2 - x
                    have g1:= h9 1
                    specialize h 1 0
                    ring_nf at h
                    rw [g1] at h
                    ring_nf at h
                    rw [h9 _] at h
                    ring_nf at h
                    replace h : f 0 * (f 0 - 1 / 2) = 0:= by linarith
                    simp [h7] at h
                    field_simp at h
                    replace h : f 0 = 1 / 2:= by linarith
                    rw [h] at h9
                    right
                    right
                    intro x
                    specialize h9 x
                    linarith
                .
                    -- Final case also leads to f(x) = 1/2 - x through a different path
                    simp at h9
                    rcases h9 with ⟨c, hc⟩
                    replace hc : f c = c - f 0:= by
                        specialize h6 c
                        simp [hc] at h6
                        exact h6
                    -- Prove that if f(c) = c - f(0) then c = f(0)
                    have H1 : ∀ c : ℝ, f c = c - f 0 → c = f 0:= by
                        intro c hc
                        specialize h5 b c
                        rw [hb, hc] at h5
                        apply sub_eq_zero.2 at h5
                        ring_nf at h5
                        replace h5 : b * (c - f 0) = 0:= by linarith
                        simp [hbne] at h5
                        replace h5 : c = f 0:= by linarith
                        exact h5
                    -- Prove that f(0) = 1/2
                    have H2 : f 0 = 1 / 2:= by
                        specialize H1 c hc
                        rw [H1] at hc
                        simp at hc
                        specialize h2 a (f 0) ha hc
                        rw [haeq] at h2
                        replace h2 : f 0 * (f 0 - 1 / 2) = 0:= by linarith
                        simp at h2
                        simp [h7] at h2
                        field_simp at h2
                        linarith
                    rw [H2] at H1 h6
                    -- Prove that for x ≠ 1/2, f(x) = -x + 1/2
                    replace h6 : ∀ x : ℝ, x ≠ 1 / 2 → f x = -x + 1 / 2:= by
                        intro x hx
                        by_contra H3
                        specialize h6 x
                        simp at H3
                        simp [H3] at h6
                        field_simp at h6
                        specialize H1 x (by linarith)
                        trivial
                    right
                    right
                    intro x
                    -- Handle both cases: x = 1/2 and x ≠ 1/2
                    by_cases hx : x = 1 / 2
                    .
                        subst x
                        rw [H2] at hc
                        specialize H1 c hc
                        rw [H1] at hc
                        exact hc
                    .
                        specialize h6 x hx
                        linarith
    .
        -- Reverse direction: prove that each of the three possible functions satisfies the original equation
        intro h
        rcases h with h | h | h
        all_goals
            simp [h]
            intro x y
            ring_nf
