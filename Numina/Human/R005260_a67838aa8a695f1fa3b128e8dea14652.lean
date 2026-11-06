import Mathlib

/- Soit $x, y, z$ trois réels positifs, tel que $x \leqslant 1$. Démontrer que:

$$
x y+y+2 z \geqslant 4 \sqrt{x y z}
$$ -/
theorem algebra_607235 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x ≤ 1) :
    x * y + y + 2 * z ≥ 4 * √(x * y * z) := by
        -- First, prove that (1-x)*y ≥ 0
        -- This is true because x ≤ 1 and y > 0
        have g1 : (1 - x) * y ≥ 0:= by
            replace h : 1 - x ≥ 0:= by linarith
            positivity
        -- The main inequality can be reduced to: x * y + z ≥ 2*√(x * y * z)
        -- Because (1-x)*y ≥ 0, we can add this to both sides
        suffices x * y + z ≥ 2 * √(x * y * z) by linarith
        -- Prove a general AM-GM inequality: a + b ≥ 2*√(a*b) for non-negative a,b
        have g2 : ∀ a b : ℝ, a ≥ 0 → b ≥ 0 → a + b ≥ 2 * √(a * b) := by
            intro a b ha hb
            -- Use the fact that (√a - √b)² ≥ 0
            have g3 : (√a - √b) ^ 2 ≥ 0:= by positivity
            ring_nf at g3
            -- Simplify √a² = a and √b² = b using positivity
            rw [show √a ^ 2 = a by exact Real.sq_sqrt ha] at g3
            rw [show √b ^ 2 = b by exact Real.sq_sqrt hb] at g3
            -- Use the property √(a*b) = √a * √b
            rw [show √a * √b = √(a * b) by exact Eq.symm (Real.sqrt_mul' a hb)] at g3
            linarith
        -- Apply the AM-GM inequality to x*y and z
        specialize g2 (x * y) z (by positivity) (by positivity)
        exact g2
