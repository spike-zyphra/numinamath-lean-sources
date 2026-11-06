import Mathlib
/- Vind alle drietallen reële getallen $(x, y, z)$ die voldoen aan

$$
x^{2}+y^{2}+z^{2}+1=x y+y z+z x+|x-2 y+z|
$$ -/
theorem algebra_604443 : {(x, y, z) : ℝ × ℝ × ℝ | x ^ 2 + y ^ 2 + z ^ 2 + 1 = x * y + y * z + z * x + |x - 2 * y + z|} =
{(x, y, z) : ℝ × ℝ × ℝ | ∃ t : ℝ, (x, y, z) = (t + 1, t, t + 1) ∨ (x, y, z) = (t - 1, t, t - 1)}:= by
    -- Prove equality of sets by showing double inclusion
    ext ⟨x, y, z⟩
    constructor
    .
        -- Forward direction: if (x,y,z) satisfies the equation, it has the required form
        intro h
        simp at h
        -- Rearrange the equation into a sum of squares form
        replace h : 1 / 2 * (x - y) ^ 2 + 1 / 2 * (z - y) ^ 2 + 1 / 2 * (x - y - (z - y)) ^ 2 + 1 = |x - 2 * y + z|:= by linarith
        -- Rewrite the absolute value term
        rw [show x - 2 * y + z = x - y + (z - y) by ring] at h
        -- Introduce substitutions for simpler expressions
        set a:= x - y with ha
        set b:= z - y with hb
        clear_value a b
        -- Use non-negativity of squares
        have g1 : (a - b) ^ 2 ≥ 0:= by positivity
        have g2 : (a + b) ^ 2 = |a + b| ^ 2:= by exact Eq.symm (sq_abs (a + b))
        have g3 : (|a + b| - 2) ^ 2 ≥ 0:= by positivity
        -- Deduce that certain expressions must be zero
        replace g1 : (a - b) ^ 2 = 0:= by linarith
        replace g3 : (|a + b| - 2) ^ 2 = 0:= by linarith
        simp at g1 g3
        -- Conclude a = b
        replace g1 : a = b:= by linarith
        rw [g1] at g3
        ring_nf at g3
        -- Use properties of absolute value
        rw [show |b * 2| = |b| * |2| by exact abs_mul b 2] at g3
        norm_num at g3
        -- Deduce |b| = 1
        replace g3 : |b| = 1:= by linarith
        replace g3 : b = 1 ∨ b = -1:= by exact eq_or_eq_neg_of_abs_eq g3
        -- Case analysis on b = 1 or b = -1
        rcases g3 with g3 | g3
        .
            -- Case b = 1: leads to solution (t+1, t, t+1)
            rw [g1, g3] at ha
            rw [g3] at hb
            replace ha : x = y + 1:= by linarith
            replace hb : z = y + 1:= by linarith
            subst x z
            simp
        .
            -- Case b = -1: leads to solution (t-1, t, t-1)
            rw [g1, g3] at ha
            rw [g3] at hb
            replace ha : x = y - 1:= by linarith
            replace hb : z = y - 1:= by linarith
            subst x z
            simp
    .
        -- Backward direction: verify that the proposed solutions satisfy the equation
        intro h
        simp at h
        rcases h with ⟨t, h⟩
        rcases h with h | h
        all_goals
            rcases h with ⟨h1, h2, h3⟩
            subst x y z
            simp
            ring_nf
            norm_num
            linarith
