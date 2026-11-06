import Mathlib

open Real Set
open scoped BigOperators

/- Find the range of the function

\[m(x) = \sqrt{x + 5} + \sqrt{20 - x}.\] -/
theorem algebra_18559 (m : ℝ → ℝ) (S : Set ℝ) (hS : S = Icc (-5) 20) (hm : m = λ x => sqrt (x + 5) + sqrt (20 - x)) :
    m '' S = {y | 5 ≤ y ∧ y ≤ 5 * sqrt 2} := by
    -- substitute m and S into the equation
    rw [hm]
    simp [Set.image, hS]
    -- simplify the equation
    ext x
    -- lemma : 5 * \sqrt{2} = \sqrt{50}
    have h6 : 5 * sqrt 2 = √50 := by
        rw [show 5 * sqrt 2 = √(5 * 5 * 2) by field_simp]
        norm_num
    -- split the goal into two
    constructor <;> intro h
    .   -- first goal : y ∈ m '' S → 5 ≤ y ∧ y ≤ √50
        simp at h
        -- introduce a, ha, ha1, ha2, ha3
        rcases h with ⟨a, ha⟩
        rcases ha with ⟨⟨ha1, ha2⟩, ha3⟩
        -- replace x with a in the equation
        rw [←ha3]
        -- simplify the expression
        simp
        -- some lemmas, including nonnegativity of square roots
        have h1 : 0 ≤ √(a + 5) := sqrt_nonneg _
        have h2 : 0 ≤ √(20 - a) := sqrt_nonneg _
        have h3 : 0 ≤ √(a + 5) * √(20 - a) := mul_nonneg h1 h2
        have h4 : 0 ≤ √(a + 5) + √(20 - a) := add_nonneg h1 h2
        -- transform the equation
        have h5 : (√(a + 5) + √(20 - a)) ^ 2 = (√(a + 5)) ^ 2 + 2 * √(a + 5) * √(20 - a) + (√(20 - a)) ^ 2 := by ring
        have g1 : (√(a + 5)) ^ 2 = a + 5 := sq_sqrt (by linarith)
        have g2 : (√(20 - a)) ^ 2 = 20 - a := sq_sqrt (by linarith)
        -- split the goal into two
        constructor
        .   -- firstly : 5 ≤ √(a + 5) + √(20 - a)
            have h7 : 5 = √25 := by
                rw [show 5 = √(5 * 5) by field_simp]
                norm_num
            nth_rw 1 [h7]
            -- square the equation
            suffices 25 ≤ (√(a + 5) + √(20 - a)) ^ 2 by exact (sqrt_le_left h4).mpr this
            rw [h5, g1, g2]
            -- trivial inequality
            linarith
        .   -- secondly : √(a + 5) + √(20 - a) ≤ √50
            have h7 : √(625 / 4) = 25 / 2 := by
                rw [show 25 / 2 = √((25 / 2) * 25 / 2) by field_simp]
                norm_num
            rw [h6]
            -- square the equation
            suffices (√(a + 5) + √(20 - a)) ^ 2 ≤ 50 by exact (le_sqrt h4 (by linarith)).mpr this
            -- simplify the equation
            rw [h5, g1, g2]
            suffices √(a + 5) * √(20 - a) ≤ 25 / 2 by linarith
            -- transform the equation
            have h8 : - a * a + 15 * a + 100 = - (a - 15 / 2) ^ 2 + 625 / 4 := by ring_nf
            -- lemma to prove the inequality
            have h9 : -(a - 15 / 2) ^ 2 + 625 / 4 ≤ 625 / 4 := by linarith [pow_two_nonneg (a - 15 / 2)]
            rw [←h7]
            -- transform the inequality step by step
            calc _ = √((a + 5) * (20 - a)) := by rw [←sqrt_mul (by linarith) _]
                 _ = √(- a * a + 15 * a + 100) := by ring_nf
                 _ = √(-(a - 15 / 2) ^ 2 + 625 / 4) := by rw [h8]
                 _ ≤ √(625 / 4) := sqrt_le_sqrt h9
    .   -- second goal : 5 ≤ y ∧ y ≤ √50 → ∃ x, x ∈ S ∧ m x = y
        -- simplify the expression
        simp at h ⊢
        -- construct a
        use (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2)
        -- similar lemmas to prove nonnegativity
        have h1 : √(-(x ^ 4 - 50 * x ^ 2) / 4) ≥ 0 := sqrt_nonneg _
        -- this useful lemma already prove one of the goals
        have h2 : √(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 ≤ 20 := by
            suffices √(-(x ^ 4 - 50 * x ^ 2) / 4) ≤ 25 / 2 by linarith
            apply (sqrt_le_left (show 0 ≤ 25 / 2 by linarith)).mpr
            suffices x ^ 4 - 50 * x ^ 2 + 625 ≥ 0 by linarith
            rw [show x ^ 4 - 50 * x ^ 2 + 625 = (x ^ 2 - 25) ^ 2 by ring_nf]
            positivity
        -- split h
        rcases h with ⟨hx1, hx2⟩
        -- split the goal into two
        refine ⟨⟨?_, h2⟩, ?_⟩
        .   -- trivial inequality
            linarith [h1]
        .   -- prove the equation
            have gx : 5 ^ 2 ≤ x ^ 2 := sq_le_sq' (by linarith) (by linarith)
            -- some lemmas of transformation
            have g1 : (√(√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5) + √(20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2))) ^ 2 = (√(√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5)) ^ 2 + 2 * √(√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5) * √(20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2)) + (√(20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2))) ^ 2 := by ring
            have g2 : (√(√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5)) ^ 2 = √(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5 := sq_sqrt (by linarith)
            have g3 : (√(20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2))) ^ 2 = 20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2) := sq_sqrt (by linarith)
            have g4 : √(√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5) + √(20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2)) ≥ 0 := add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)
            -- square the equation
            suffices (√(√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2 + 5) + √(20 - (√(-(x ^ 4 - 50 * x ^ 2) / 4) + 15 / 2))) ^ 2 = x ^ 2 by exact (sq_eq_sq g4 (show 0 ≤ x by linarith)).mp this
            -- use the lemmas to simplify the equation
            rw [g1, g2, g3]
            -- transform the equation
            ring_nf
            -- transform the equation
            suffices √(25 / 2 + √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))) * √(25 / 2 - √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))) = (x ^ 2 - 25) / 2 by linarith
            -- square the equation
            suffices (√(25 / 2 + √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))) * √(25 / 2 - √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4)))) ^ 2 = ((x ^ 2 - 25) / 2) ^ 2 by exact (sq_eq_sq (show 0 ≤ √(25 / 2 + √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))) * √(25 / 2 - √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))) by exact mul_nonneg (sqrt_nonneg (25 / 2 + √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4)))) (sqrt_nonneg (25 / 2 - √(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))))) (show 0 ≤ (x ^ 2 - 25) / 2 by linarith)).mp this
            -- use the lemmas to simplify the equation
            ring_nf at g2 g3 ⊢
            rw [g2, g3]
            ring_nf
            -- one last nonnegativity to prove
            rw [h6] at hx2
            -- first simplify the hypothesis
            replace hx2 : x ^ 2 ≤ √50 ^ 2 := sq_le_sq' (by linarith) (by linarith)
            simp at hx2
            -- lemma to prove the nonnegativity
            have g5 : 0 ≤ x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4) := by
                -- transform the inequality
                suffices 0 ≤ (x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4)) * 4 by linarith
                ring_nf
                -- transform the inequality
                rw [show x ^ 2 * 50 - x ^ 4 = x ^ 2 * (50 - x ^ 2) by ring_nf]
                exact mul_nonneg (by linarith) (by linarith)
            -- transform the square and sqrt, using the lemma
            rw [show (√(x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4))) ^ 2 = x ^ 2 * (25 / 2) + x ^ 4 * (-1 / 4) by exact sq_sqrt (by linarith)]
            -- trivial calculation
            ring_nf
