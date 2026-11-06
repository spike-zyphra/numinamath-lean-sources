import Mathlib
/- Soit $a, b$ et $c$ trois réels strictement positifs. Démontrer que

$$
4\left(a^{3}+b^{3}+c^{3}+3\right) \geqslant 3(a+1)(b+1)(c+1) .
$$ -/
theorem algebra_605586 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3) ≥ 3 * (a + 1) * (b + 1) * (c + 1) := by
    -- First lemma: For positive x, y, z, proves x³ + y³ + z³ ≥ 3xyz
    -- This is a well-known inequality related to the symmetric mean inequality
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- The key identity: x³ + y³ + z³ - 3xyz = 1/2(x+y+z)((x-y)² + (y-z)² + (z-x)²)
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity
    -- Apply the first lemma to (a+1), (b+1), (c+1)
    specialize h1 (a + 1) (b + 1) (c + 1) (by positivity) (by positivity) (by positivity)
    -- Second lemma: For positive x, proves 4(x³ + 1) ≥ (x+1)³
    -- This inequality helps connect the LHS and RHS of the main theorem
    have h2 : ∀ x : ℝ, x > 0 → 4 * (x ^ 3 + 1) ≥ (x + 1) ^ 3:= by
        intro x hx
        -- Uses the fact that (x+1)(x-1)² ≥ 0 for positive x
        have h2 : (x + 1) * (x - 1) ^ 2 ≥ 0:= by positivity
        linarith
    -- Apply the second lemma to a, b, and c respectively
    have h3:= h2 a ha
    have h4:= h2 b hb
    have h5:= h2 c hc
    -- Combine all inequalities to prove the main theorem
    linarith
