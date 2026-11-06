import Mathlib
/- Let $a, b, c$ be positive real numbers such that $a+b+c=4 \sqrt[3]{a b c}$. Prove that  $$ 2(a b+b c+c a)+4 \min \left(a^{2}, b^{2}, c^{2}\right) \geq a^{2}+b^{2}+c^{2} $$ -/
theorem algebra_605118 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(h : a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3)) :
2 * (a * b + b * c + c * a) + 4 * min (min (a ^ 2) (b ^ 2)) (c ^ 2) ≥ a ^ 2 + b ^ 2 + c ^ 2:= by

    -- Helper lemma: proves the inequality when c is the minimum value
    have h1 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a ≥ c ∧ b ≥ c → a + b + c = 4 * (a * b * c) ^ ((1 : ℝ) / 3) → 2 * (a * b + b * c + c * a) + 4 * c ^ 2 ≥ a ^ 2 + b ^ 2 + c ^ 2:= by
        intro a b c ha hb hc ⟨h1, h2⟩ h

        -- Normalize variables by dividing by c
        set x:= a / c with hx
        set y:= b / c with hy
        clear_value x y
        replace h : x + y + 1 = 4 * (x * y) ^ ((1 : ℝ) / 3):= by
            subst x y
            field_simp
            rw [show 4 * (a * b / (c * c)) ^ ((1 : ℝ) / 3) * c = 4 * (a * b / (c * c)) ^ ((1 : ℝ) / 3) * c ^ (1 : ℝ) by simp]
            rw [show c ^ (1 : ℝ) = c ^ ((3 : ℝ) * (1 / 3)) by ring_nf]
            rw [show 4 * (a * b / (c * c)) ^ ((1 : ℝ) / 3) * c ^ ((3 : ℝ) * (1 / 3)) = 4 * ((a * b / (c * c)) ^ ((1 : ℝ) / 3) * c ^ ((3 : ℝ) * (1 / 3))) by ring]
            rw [Real.rpow_mul (by linarith) 3 (1 / 3)]
            rw [show c ^ (3 : ℝ) = c ^ 3 by norm_cast]
            rw [Eq.symm (Real.mul_rpow (by positivity) (by positivity))]
            rw [show a * b / (c * c) * c ^ 3 = a * b * c by field_simp ; linarith]
            exact h
        replace hy : b = c * y:= by rw [hy] ; field_simp
        replace hx : a = c * x:= by rw [hx] ; field_simp
        subst a b
        replace ha : x > 0:= by exact (pos_iff_pos_of_mul_pos ha).mp hc
        replace hb : y > 0:= by exact (pos_iff_pos_of_mul_pos hb).mp hc
        suffices c ^ 2 * (2 * (x * y + x + y) + 4) ≥ c ^ 2 * (x ^ 2 + y ^ 2 + 1) by linarith
        have g1 : c ^ 2 > 0:= by positivity
        suffices 2 * (x * y + x + y) + 4 ≥ x ^ 2 + y ^ 2 + 1 by exact (mul_le_mul_iff_of_pos_left g1).mpr this
        clear g1 hc h1 h2 c
        suffices 4 * (x * y) + 2 * (x + y) + 3 ≥ (x + y) ^ 2 by linarith
        set t:= (x * y) ^ ((1 : ℝ) / 3) with ht
        replace h : x + y = 4 * t - 1:= by linarith
        have ht1 : x * y = t ^ 3:= by
            rw [ht]
            rw [show ((x * y) ^ ((1 : ℝ) / 3)) ^ 3 = ((x * y) ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast]
            rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) 3)]
            ring_nf
            simp
        rw [h, ht1]
        suffices t * (t - 2) ^ 2 ≥ 0 by linarith
        positivity

    -- Case analysis: one of a, b, or c must be the minimum value
    have h2 : (a ≥ c ∧ b ≥ c) ∨ (a ≥ b ∧ c ≥ b) ∨ (b ≥ a ∧ c ≥ a):= by
        by_cases g1 : a ≥ b
        .
            -- If a ≥ b, check if c ≥ b to determine minimum
            by_cases g2 : c ≥ b
            .
                right
                left
                exact ⟨g1, g2⟩
            .
                simp at g2
                left
                exact ⟨(by linarith), (by linarith)⟩
        .
            -- If a < b, check if c ≥ a to determine minimum
            simp at g1
            by_cases g2 : c ≥ a
            .
                right
                right
                exact ⟨(by linarith), (by linarith)⟩
            .
                simp at g2
                left
                exact ⟨(by linarith), (by linarith)⟩

    -- Handle each case based on which value is minimum
    rcases h2 with h2 | h2 | h2
    .
        -- Case 1: c is minimum
        rcases h2 with ⟨g1, g2⟩
        specialize h1 a b c ha hb hc ⟨g1, g2⟩ h
        replace g1 : a ^ 2 ≥ c ^ 2:= by
            have g3 : a - c ≥ 0:= by linarith
            suffices (a - c) * (a + c) ≥ 0 by linarith
            positivity
        replace g2 : b ^ 2 ≥ c ^ 2:= by
            have g3 : b - c ≥ 0:= by linarith
            suffices (b - c) * (b + c) ≥ 0 by linarith
            positivity
        have g3 : min (a ^ 2) (b ^ 2) ≥ c ^ 2:= by exact le_min g1 g2
        rw [show min (min (a ^ 2) (b ^ 2)) (c ^ 2) = c ^ 2 by exact min_eq_right g3]
        exact h1
    .
        -- Case 2: b is minimum
        rcases h2 with ⟨g1, g2⟩
        specialize h1 a c b ha hc hb ⟨g1, g2⟩ (by rw [show a * c * b = a * b * c by ring] ; linarith)
        replace g1 : a ^ 2 ≥ b ^ 2:= by
            have g3 : a - b ≥ 0:= by linarith
            suffices (a - b) * (a + b) ≥ 0 by linarith
            positivity
        replace g2 : c ^ 2 ≥ b ^ 2:= by
            have g3 : c - b ≥ 0:= by linarith
            suffices (c - b) * (c + b) ≥ 0 by linarith
            positivity
        rw [show min (a ^ 2) (b ^ 2) = b ^ 2 by exact min_eq_right g1]
        rw [show min (b ^ 2) (c ^ 2) = b ^ 2 by exact min_eq_left g2]
        linarith
    .
        -- Case 3: a is minimum
        rcases h2 with ⟨g1, g2⟩
        specialize h1 b c a hb hc ha ⟨g1, g2⟩ (by rw [show b * c * a = a * b * c by ring] ; linarith)
        replace g1 : b ^ 2 ≥ a ^ 2:= by
            have g3 : b - a ≥ 0:= by linarith
            suffices (b - a) * (b + a) ≥ 0 by linarith
            positivity
        replace g2 : c ^ 2 ≥ a ^ 2:= by
            have g3 : c - a ≥ 0:= by linarith
            suffices (c - a) * (c + a) ≥ 0 by linarith
            positivity
        rw [show min (a ^ 2) (b ^ 2) = a ^ 2 by exact min_eq_left g1]
        rw [show min (a ^ 2) (c ^ 2) = a ^ 2 by exact min_eq_left g2]
        linarith
