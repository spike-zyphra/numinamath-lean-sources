import Mathlib

/- Prove that for all positive real numbers $a, b$, and $c$,

$$
\frac{a^{3}}{b c}+\frac{b^{3}}{c a}+\frac{c^{3}}{a b} \geq a+b+c
$$

and determine when equality occurs.

Each of the inequalities used in the solutions below has the property that equality holds if and only if $a=b=c$. Thus equality holds for the given inequality if and only if $a=b=c$. -/

-- Main theorem: proves the inequality and characterizes the equality case
theorem algebra_604793 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
  a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) ≥ a + b + c ∧ (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) = a + b + c ↔ a = b ∧ b = c):= by
    -- Lemma 1: For positive x,y,z, proves x³/(yz) + y + z ≥ 3x with equality iff y=z
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 / (y * z) + y + z ≥ 3 * x ∧ (x ^ 3 / (y * z) + y + z = 3 * x → y = z):= by
      -- Lemma 2: Proves x³ + y³ + z³ - 3xyz ≥ 0 with equality iff y=z
      have h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0 ∧ (x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 0 → y = z):= by
        intro x y z hx hy hz
        -- Key identity: expresses the difference as sum of squares
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        constructor
        .
          positivity
        .
          -- Proves equality case using contradiction
          intro hgoal
          suffices y - z = 0 by linarith
          by_contra H
          replace H : (y - z) ^ 2 > 0:= by positivity
          have _ : (x - y) ^ 2 + (z - x) ^ 2 ≥ 0:= by positivity
          have g2 : 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) > 0:= by positivity
          linarith
      -- Transforms Lemma 2 using cube roots
      replace h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 ∧ (x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 = 0 → y = z):= by
        intro x y z hx hy hz
        specialize h2 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        rw [show (x ^ ((1 : ℝ) / 3)) ^ 3 = (x ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h2
        rw [show (y ^ ((1 : ℝ) / 3)) ^ 3 = (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h2
        rw [show (z ^ ((1 : ℝ) / 3)) ^ 3 = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast] at h2
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h2
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h2
        rw [(Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3))] at h2
        rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h2
        rw [Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at h2
        rw [Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at h2
        simp at h2
        constructor
        .
          simp
          linarith
        .
          replace h2:= h2.2
          simp
          intro hgoal
          replace h2:= h2 hgoal
          field_simp at h2
          replace h2 : (y ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = (z ^ ((1 : ℝ) / 3)) ^ (3 : ℝ):= by rw [h2]
          rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3)] at h2
          rw [Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3)] at h2
          rw [show (1 : ℝ) / 3 * 3 = 1 by ring_nf] at h2
          simp at h2
          rw [h2]
      -- Apply lemma h2 with substituted values x^3/(yz), y, and z
      intro x y z hx hy hz
      specialize h2 (x ^ 3 / (y * z)) y z (by positivity) hy hz
      -- Simplify x^3/(yz) * y * z to x^3
      rw [show x ^ 3 / (y * z) * y * z = x ^ 3 by field_simp ; linarith] at h2
      -- Convert natural power to real power
      rw [show x ^ 3 = x ^ (3 : ℝ) by norm_cast] at h2
      -- Use property of real powers: (x^3)^(1/3) = x
      rw [Eq.symm (Real.rpow_mul (by linarith) 3 (1 / 3))] at h2
      -- Simplify 3 * (1/3) = 1
      rw [show 3 * ((1 : ℝ) / 3) = 1 by linarith] at h2
      simp at h2
      norm_cast at h2
      -- Split the conjunction into its components
      rcases h2 with ⟨h2, h2eq⟩
      constructor
      .
        linarith
      .
        intro hgoal
        replace h2eq:= h2eq (by linarith)
        rw [h2eq]

    -- Apply lemma h1 to all cyclic permutations of a, b, c
    have h2:= h1 a b c ha hb hc
    have h3:= h1 b c a hb hc ha
    have h4:= h1 c a b hc ha hb
    -- Split each result into inequality and equality cases
    rcases h2 with ⟨h2, h2eq⟩
    rcases h3 with ⟨h3, h3eq⟩
    rcases h4 with ⟨h4, _⟩
    constructor
    .
      -- Combine the three inequalities
      linarith
    .
      constructor
      .
        -- Forward direction: if equality holds, then a=b=c
        intro hgoal
        replace h2eq:= h2eq (by linarith)
        replace h3eq:= h3eq (by linarith)
        constructor
        all_goals
        linarith
      .
        -- Reverse direction: if a=b=c, then equality holds
        intro ⟨g1, g2⟩
        rw [g1, g2]
        field_simp
        linarith
