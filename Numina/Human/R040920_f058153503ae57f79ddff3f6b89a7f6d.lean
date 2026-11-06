import Mathlib
/- Bewijs dat voor alle positieve reële getallen $a, b, c$ geldt:

$$
a+\sqrt{a b}+\sqrt{3}{a b c} \leq \frac{4}{3}(a+b+c)
$$ -/
theorem algebra_605845 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + √(a * b) + (a * b * c) ^ ((1 : ℝ) / 3) ≤
    (4 / 3) * (a + b + c) := by
    -- First, prove a helper lemma about the sum of cubes
    -- For any positive real numbers x, y, z:
    -- x³ + y³ + z³ - 3xyz ≥ 0
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- Express the sum of cubes in terms of squares of differences
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Transform the first lemma to work with cube roots
    -- For positive x, y, z:
    -- x + y + z - 3(xyz)^(1/3) ≥ 0
    replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
        intro x y z hx hy hz
        specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        -- Series of rewrites to handle exponents and cube roots
        rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h1
        rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h1
        rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h1
        rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h1
        simp at h1
        simp
        linarith

    -- Second helper lemma: AM-GM inequality for two numbers
    -- For positive x, y:
    -- x + y ≥ 2√(xy)
    have h2 : ∀ x y : ℝ, x > 0 → y > 0 → x + y ≥ 2 * √(x * y) := by
        intro x y hx hy
        -- Proof using (√x - √y)² ≥ 0
        have g3 : (√x - √y) ^ 2 ≥ 0:= by positivity
        ring_nf at g3
        rw [show √x ^ 2 = x by exact Real.sq_sqrt (by positivity)] at g3
        rw [show √y ^ 2 = y by exact Real.sq_sqrt (by positivity)] at g3
        rw [show √x * √y = √(x * y) by exact Eq.symm (Real.sqrt_mul' x (by positivity))] at g3
        linarith

    -- Apply the lemmas with carefully chosen values
    -- Use h1 with (a/4, b, 4c)
    specialize h1 (a / 4) b (4 * c) (by positivity) (by positivity) (by positivity)
    -- Use h2 with (a/2, 2b)
    specialize h2 (a / 2) (2 * b) (by positivity) (by positivity)
    -- Simplify the algebraic expressions
    rw [show a / 4 * b * (4 * c) = a * b * c by ring_nf] at h1
    rw [show a / 2 * (2 * b) = a * b by ring_nf] at h2
    -- Complete the proof using linear arithmetic
    linarith
