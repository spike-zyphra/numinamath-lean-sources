import Mathlib
/- . Let $a, b, c$ be positive numbers such that $a b+b c+c a=3$. Prove that

$$
a+b+c \geq a b c+2
$$ -/
theorem inequalities_606059 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = 3) : a + b + c ≥ a * b * c + 2 := by
        -- Main proof strategy: First prove for ordered case (a ≥ b ≥ c), then handle all permutations
        have h1 : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → a ≥ b → b ≥ c → a * b + b * c + c * a = 3 → a + b + c ≥ a * b * c + 2:= by
            intro a b c ha hb hc h1 h2 h
            -- Prove that a*b is bounded: 1 ≤ a*b ≤ 3
            have g1 : a * b ≥ 1:= by
                have g1 : a * b ≥ b * c:= by
                    have g1 : a - c ≥ 0:= by linarith
                    replace g1 : b * (a - c) ≥ 0:= by positivity
                    linarith
                have g2 : a * b ≥ c * a:= by
                    have g2 : b - c ≥ 0:= by linarith
                    replace g2 : a * (b - c) ≥ 0:= by positivity
                    linarith
                linarith
            have g2 : a * b ≤ 3:= by
                have g2 : b * c ≥ 0:= by positivity
                have g3 : c * a ≥ 0:= by positivity
                linarith
            -- Express c in terms of a and b
            replace h : c = (3 - a * b) / (a + b):= by field_simp ; linarith
            -- Apply AM-GM inequality: a + b ≥ 2√(ab)
            have h3 : a + b ≥ 2 * √(a * b):= by
                have g1 : (√a - √b) ^ 2 ≥ 0:= by positivity
                ring_nf at g1
                rw [show √a ^ 2 = a by refine Real.sq_sqrt (by linarith)] at g1
                rw [show √b ^ 2 = b by refine Real.sq_sqrt (by linarith)] at g1
                rw [show √a * √b = √(a * b) by field_simp] at g1
                linarith
            -- Let x = √(ab) to simplify expressions
            set x:= √(a * b) with hx
            clear_value x
            suffices 2 * x + (1 - a * b) * c ≥ 2 by linarith
            rw [h]
            rw [show (1 - a * b) * ((3 - a * b) / (a + b)) = -(((a * b - 1) * (3 - a * b)) / (a + b)) by ring]
            -- Use x^2 = ab to simplify expressions
            have h4 : x ^ 2 = a * b:= by
                rw [hx]
                refine Real.sq_sqrt (by positivity)
            rw [←h4]
            -- Prove x ≥ 1 using earlier bound on ab
            have h5 : x ≥ 1:= by
                rw [hx]
                exact Real.one_le_sqrt.mpr g1
            -- Key inequalities for final step
            have g3 : x ^ 2 - 1 ≥ 0:= by
                rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
                exact mul_nonneg (by linarith) (by linarith)
            have g4 : 3 - x ^ 2 ≥ 0:= by linarith
            replace g4 : (x ^ 2 - 1) * (3 - x ^ 2) ≥ 0:= by positivity
            -- Final algebraic manipulations
            have h6 : (x ^ 2 - 1) * (3 - x ^ 2) / (a + b) ≤ (x ^ 2 - 1) * (3 - x ^ 2) / (2 * x):= by refine div_le_div_of_nonneg_left g4 (by linarith) h3
            suffices 2 * x - (x ^ 2 - 1) * (3 - x ^ 2) / (2 * x) ≥ 2 by linarith
            replace g4 : 2 * x > 0:= by linarith
            suffices (2 * x - (x ^ 2 - 1) * (3 - x ^ 2) / (2 * x)) * (2 * x) ≥ 2 * (2 * x) by exact le_of_mul_le_mul_right this g4
            clear h1 h2 h3 h4 h5 h6 g1 g2 g3 h ha hb hc
            rw [show (2 * x - (x ^ 2 - 1) * (3 - x ^ 2) / (2 * x)) * (2 * x) = x ^ 4 + 3 by field_simp ; linarith]
            have h1 : (x - 1) ^ 2 * (2 + (x + 1) ^ 2) ≥ 0:= by positivity
            linarith
        -- Handle all possible orderings of a, b, c using case analysis
        by_cases ga : a ≥ b
        .
            by_cases gb : b ≥ c
            .
                -- Case a ≥ b ≥ c
                specialize h1 a b c ha hb hc ga gb h
                exact h1
            .
                simp at gb
                by_cases gc : c ≥ a
                .
                    -- Case c ≥ a ≥ b
                    specialize h1 c a b hc ha hb gc (by linarith) (by linarith)
                    linarith
                .
                    -- Case a ≥ c > b
                    simp at gc
                    specialize h1 a c b ha hc (by linarith) (by linarith) (by linarith) (by linarith)
                    linarith
        .
            simp at ga
            by_cases gb : b ≥ c
            .
                by_cases gc : c ≥ a
                .
                    -- Case b ≥ c ≥ a
                    specialize h1 b c a hb hc ha gb gc (by linarith)
                    linarith
                .
                    -- Case b > a > c
                    simp at gc
                    specialize h1 b a c hb ha hc (by linarith) (by linarith) (by linarith)
                    linarith
            .
                -- Case c > b > a
                simp at gb
                specialize h1 c b a hc hb ha (by linarith) (by linarith) (by linarith)
                linarith
