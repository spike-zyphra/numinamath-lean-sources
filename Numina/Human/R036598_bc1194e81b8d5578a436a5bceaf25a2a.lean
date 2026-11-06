import Mathlib

set_option maxHeartbeats 400000

open Real

/- $4 Let $a, b, c \in \mathbf{R}^{+}$, and $a b c=1$. Prove:
$$\sum_{\mathrm{oc}} \frac{a b}{a^{5}+b^{5}+a b} \leqslant 1$$
and ask when the equality holds? -/

theorem inequalities_599117 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1) :
    a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) ≤ 1 ∧
    (a * b / (a ^ 5 + b ^ 5 + a * b) +
     b * c / (b ^ 5 + c ^ 5 + b * c) +
     c * a / (c ^ 5 + a ^ 5 + c * a) = 1 ↔
     a = 1 ∧ b = 1 ∧ c = 1) := by

     -- we first show the strict inequality when the conditions are not held
    have s: ¬ (a = b ∧ b = c) → a * b / (a ^ 5 + b ^ 5 + a * b) +
    b * c / (b ^ 5 + c ^ 5 + b * c) +
    c * a / (c ^ 5 + a ^ 5 + c * a) < 1 := by
        intro l
        replace l: a ≠ b ∨ b ≠ c := by
            simp at l
            by_cases r: a = b
            .
                simp [r] at l
                right
                simp
                exact l
            .
                left
                simp
                exact r
        
        rcases l with l | l

        -- case 1: a ≠ b
        .   
            -- we show the strict inequality on a side
            have la: a * b / (a ^ 5 + b ^ 5 + a * b) < c / (a + b + c) := by
                -- we show the key inequality
                have h1: a ^ 2 * b ^ 2 * (a + b) < a ^ 5 + b ^ 5 := by
                    have o: 0 < a ^ 5 + b ^ 5 - (a ^ 2 * b ^ 2 * (a + b)) := by
                        rw [show a ^ 5 + b ^ 5 - (a ^ 2 * b ^ 2 * (a + b)) = 
                        (a ^ 2 - b ^ 2) * (a ^ 3 - b ^ 3) by ring]
                        by_cases t: a < b
                        .
                            rw [show (a ^ 2 - b ^ 2) * (a ^ 3 - b ^ 3) = 
                            (b ^ 2 - a ^ 2) * (b ^ 3 - a ^ 3) by ring]
                            have f1: 0 < b ^ 2 - a ^ 2 := by
                                nlinarith
                            have f2: 0 < b ^ 3 - a ^ 3 := by
                                nlinarith
                            nlinarith
                        .   
                            simp at t
                            replace t: b < a := by
                                by_contra! o
                                replace o: b = a := by linarith
                                simp [o] at l
                            have f1: 0 < a ^ 2 - b ^ 2 := by
                                nlinarith
                            have f2: 0 < a ^ 3 - b ^ 3 := by
                                nlinarith
                            nlinarith
                    nlinarith
                rw [show a * b / (a ^ 5 + b ^ 5 + a * b) = 
                a ^ 2 * b ^ 2 * c / ((a ^ 5 + b ^ 5) * (a * b * c) + a ^ 2 * b ^ 2 * c) by field_simp; ring]
                simp [h]
                rw [show c / (a + b + c) =
                 a ^ 2 * b ^ 2 * c / (a ^ 2 * b ^ 2 * (a + b) + a ^ 2 * b ^ 2 * c) by field_simp; ring]
                apply div_lt_div_of_pos_left
                nlinarith
                positivity
                nlinarith

            -- we show the inequality on b side, not strict
            have lb: b * c / (b ^ 5 + c ^ 5 + b * c) ≤ a / (b + c + a) := by
                -- we show the key inequality
                have h2: b ^ 2 * c ^ 2 * (b + c) ≤ b ^ 5 + c ^ 5 := by
                    have o: 0 ≤ b ^ 5 + c ^ 5 - (b ^ 2 * c ^ 2 * (b + c)) := by
                        rw [show b ^ 5 + c ^ 5 - (b ^ 2 * c ^ 2 * (b + c)) = 
                        (b ^ 2 - c ^ 2) * (b ^ 3 - c ^ 3) by ring]
                        by_cases t: b < c
                        .
                            rw [show (b ^ 2 - c ^ 2) * (b ^ 3 - c ^ 3) = 
                            (c ^ 2 - b ^ 2) * (c ^ 3 - b ^ 3) by ring]
                            have f1: 0 < c ^ 2 - b ^ 2 := by
                                nlinarith
                            have f2: 0 < c ^ 3 - b ^ 3 := by
                                nlinarith
                            nlinarith
                        .   
                            simp at t
                            replace t: c ≤ b := by
                                nlinarith
                            have f1: 0 ≤ b ^ 2 - c ^ 2 := by
                                nlinarith
                            have f2: 0 ≤ b ^ 3 - c ^ 3 := by
                                nlinarith
                            nlinarith
                    nlinarith
                rw [show b * c / (b ^ 5 + c ^ 5 + b * c) = 
                b ^ 2 * c ^ 2 * a / ((b ^ 5 + c ^ 5) * (a * b * c) + b^2 * c^2 * a) by field_simp; ring]
                simp [h]
                rw [show a / (b + c + a) =
                 b ^ 2 * c ^ 2 * a / (b ^ 2 * c ^ 2 * (b + c) + b ^ 2 * c ^ 2 * a) by field_simp; ring]
                apply div_le_div_of_nonneg_left
                nlinarith
                positivity
                nlinarith
            
            -- we show the inequality on c side, not strict
            have lc: c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (c + a + b) := by
                -- we show the key inequality
                have h3: c ^ 2 * a ^ 2 * (c + a) ≤ c ^ 5 + a ^ 5 := by
                    have o: 0 ≤ c ^ 5 + a ^ 5 - (c ^ 2 * a ^ 2 * (c + a)) := by
                        rw [show c ^ 5 + a ^ 5 - (c ^ 2 * a ^ 2 * (c + a)) = 
                        (c ^ 2 - a ^ 2) * (c ^ 3 - a ^ 3) by ring]
                        by_cases t: c < a
                        .
                            rw [show (c ^ 2 - a ^ 2) * (c ^ 3 - a ^ 3) = 
                            (a ^ 2 - c ^ 2) * (a ^ 3 - c ^ 3) by ring]
                            have f1: 0 < a ^ 2 - c ^ 2 := by
                                nlinarith
                            have f2: 0 < a ^ 3 - c ^ 3 := by
                                nlinarith
                            nlinarith
                        .   
                            simp at t
                            replace t: a ≤ c := by
                                nlinarith
                            have f1: 0 ≤ c^2 - a^2 := by
                                nlinarith
                            have f2: 0 ≤ c^3 - a^3 := by
                                nlinarith
                            nlinarith
                    nlinarith
                rw [show c * a / (c^5 + a^5 + c*a) = 
                c^2 * a^2 * b / ((c^5 + a^5) * (a*b*c) + c^2*a^2*b) by field_simp; ring]
                simp [h]
                rw [show b / (c + a + b) =
                 c^2 * a^2 * b / (c^2*a^2*(c+a)+c^2*a^2*b) by field_simp; ring]
                apply div_le_div_of_nonneg_left
                nlinarith
                positivity
                nlinarith

            -- combine la lb lc
            rw [show 1 = c / (a + b + c) + b / (c + a + b) + a / (b + c + a) by
                field_simp; ring]
            nlinarith

        -- case 2: b ≠ c, just similar as case 1
        .

            -- we show the inequality on a side, not strict
            have la: a * b / (a ^ 5 + b ^ 5 + a * b) ≤ c / (a + b + c) := by
                -- we show the key inequality
                have h1: a ^ 2 * b ^ 2 * (a + b) ≤ a ^ 5 + b ^ 5 := by
                    have o: 0 ≤ a ^ 5 + b ^ 5 - (a ^ 2 * b ^ 2 * (a + b)) := by
                        rw [show a ^ 5 + b ^ 5 - (a ^ 2 * b ^ 2 * (a + b)) = 
                        (a ^ 2 - b ^ 2) * (a ^ 3 - b ^ 3) by ring]
                        by_cases t: a < b
                        .
                            rw [show (a ^ 2 - b ^ 2) * (a ^ 3 - b ^ 3) = 
                            (b ^ 2 - a ^ 2) * (b ^ 3 - a ^ 3) by ring]
                            have f1: 0 < b ^ 2 - a ^ 2 := by
                                nlinarith
                            have f2: 0 < b ^ 3 - a ^ 3 := by
                                nlinarith
                            nlinarith
                        .   
                            simp at t
                            replace t: b ≤ a := by
                               nlinarith
                            have f1: 0 ≤ a ^ 2 - b ^ 2 := by
                                nlinarith
                            have f2: 0 ≤ a ^ 3 - b ^ 3 := by
                                nlinarith
                            nlinarith
                    nlinarith
                rw [show a * b / (a ^ 5 + b ^ 5 + a * b) = 
                a ^ 2 * b ^ 2 * c / ((a ^ 5 + b ^ 5) * (a * b * c) + a ^ 2 * b ^ 2 * c) by field_simp; ring]
                simp [h]
                rw [show c / (a + b + c) =
                 a ^ 2 * b ^ 2 * c / (a ^ 2 * b ^ 2 * (a + b) + a ^ 2 * b ^ 2 * c) by field_simp; ring]
                apply div_le_div_of_nonneg_left
                nlinarith
                positivity
                nlinarith

            -- we show the strict inequality on b side
            have lb: b * c / (b ^ 5 + c ^ 5 + b * c) < a / (b + c + a) := by
                -- we show the key inequality
                have h2: b ^ 2 * c ^ 2 * (b + c) < b ^ 5 + c ^ 5 := by
                    have o: 0 < b ^ 5 + c ^ 5 - (b ^ 2 * c ^ 2 * (b + c)) := by
                        rw [show b ^ 5 + c ^ 5 - (b ^ 2 * c ^ 2 * (b + c)) = 
                        (b ^ 2 - c ^ 2) * (b ^ 3 - c ^ 3) by ring]
                        by_cases t: b < c
                        .
                            rw [show (b ^ 2 - c ^ 2) * (b ^ 3 - c ^ 3) = 
                            (c ^ 2 - b ^ 2) * (c ^ 3 - b ^ 3) by ring]
                            have f1: 0 < c ^ 2 - b ^ 2 := by
                                nlinarith
                            have f2: 0 < c ^ 3 - b ^ 3 := by
                                nlinarith
                            nlinarith
                        .   
                            simp at t
                            replace t: c < b := by
                                by_contra! o
                                replace o: c = b := by linarith
                                simp [o] at l
                            have f1: 0 < b ^ 2 - c ^ 2 := by
                                nlinarith
                            have f2: 0 < b ^ 3 - c ^ 3 := by
                                nlinarith
                            nlinarith
                    nlinarith
                rw [show b * c / (b ^ 5 + c ^ 5 + b * c) = 
                b ^ 2 * c ^ 2 * a / ((b ^ 5 + c ^ 5) * (a * b * c) + b^2 * c^2 * a) by field_simp; ring]
                simp [h]
                rw [show a / (b + c + a) =
                 b ^ 2 * c ^ 2 * a / (b ^ 2 * c ^ 2 * (b + c) + b ^ 2 * c ^ 2 * a) by field_simp; ring]
                apply div_lt_div_of_pos_left
                nlinarith
                positivity
                nlinarith
            
            -- we show the inequality on c side, not strict
            have lc: c * a / (c ^ 5 + a ^ 5 + c * a) ≤ b / (c + a + b) := by
                -- we show the key inequality
                have h3: c ^ 2 * a ^ 2 * (c + a) ≤ c ^ 5 + a ^ 5 := by
                    have o: 0 ≤ c ^ 5 + a ^ 5 - (c ^ 2 * a ^ 2 * (c + a)) := by
                        rw [show c ^ 5 + a ^ 5 - (c ^ 2 * a ^ 2 * (c + a)) = 
                        (c ^ 2 - a ^ 2) * (c ^ 3 - a ^ 3) by ring]
                        by_cases t: c < a
                        .
                            rw [show (c ^ 2 - a ^ 2) * (c ^ 3 - a ^ 3) = 
                            (a ^ 2 - c ^ 2) * (a ^ 3 - c ^ 3) by ring]
                            have f1: 0 < a ^ 2 - c ^ 2 := by
                                nlinarith
                            have f2: 0 < a ^ 3 - c ^ 3 := by
                                nlinarith
                            nlinarith
                        .   
                            simp at t
                            replace t: a ≤ c := by
                                nlinarith
                            have f1: 0 ≤ c^2 - a^2 := by
                                nlinarith
                            have f2: 0 ≤ c^3 - a^3 := by
                                nlinarith
                            nlinarith
                    nlinarith
                rw [show c * a / (c^5 + a^5 + c*a) = 
                c^2 * a^2 * b / ((c^5 + a^5) * (a*b*c) + c^2*a^2*b) by field_simp; ring]
                simp [h]
                rw [show b / (c + a + b) =
                 c^2 * a^2 * b / (c^2*a^2*(c+a)+c^2*a^2*b) by field_simp; ring]
                apply div_le_div_of_nonneg_left
                nlinarith
                positivity
                nlinarith

            -- combine la lb lc
            rw [show 1 = c / (a + b + c) + b / (c + a + b) + a / (b + c + a) by
                field_simp; ring]
            nlinarith


    -- then we can use the lemma to get the result
    constructor

    -- show the inequality
    .
        by_cases r: a = b ∧ b = c
        -- if a = b = c, then we have the equality
        .   
            rcases r with ⟨ea, eb⟩
            simp [ea, eb] at h
            have ec: c = 1 := by
                nlinarith
            simp [ec] at ea eb
            simp [ea, eb, ec]
            norm_num
        -- if a, b, c are not equal, then we have the strict inequality
        .
            simp [r] at s
            linarith
    
    -- show the condition for equality
    .
        by_cases r: a = b ∧ b = c
        -- if a = b = c, then we have the equality
        .   
            rcases r with ⟨ea, eb⟩
            simp [ea, eb] at h
            have ec: c = 1 := by
                nlinarith
            simp [ec] at ea eb
            simp [ea, eb, ec]
            norm_num
        -- if a, b, c are not equal, then we have the strict inequality
        .
            simp [r] at s
            constructor
            .
                intro i
                simp [i] at s
            .
                intro i
                simp [i] at r