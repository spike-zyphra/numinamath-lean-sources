import Mathlib
/- Let $a, b, c$ be positive real numbers such that $a+b+c=1$. Prove that

$$
\frac{7+2 b}{1+a}+\frac{7+2 c}{1+b}+\frac{7+2 a}{1+c} \geq \frac{69}{4}
$$

When does equality hold? -/
theorem algebra_605609 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 1) : (7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) ≥ 69 / 4 ∧ ((7 + 2 * b) / (1 + a) + (7 + 2 * c) / (1 + b) + (7 + 2 * a) / (1 + c) = 69 / 4 ↔ a = 1 / 3 ∧  b = 1 / 3 ∧ c = 1 / 3):= by
    -- First lemma: For positive x, y, z, proves x³ + y³ + z³ - 3xyz ≥ 0
    -- This is equivalent to Schur's inequality
    have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
        intro x y z hx hy hz
        -- Rewrite using the sum of squares formula
        have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
        rw [h1]
        positivity

    -- Transform the first lemma to work with cube roots
    -- This gives: x + y + z - 3(xyz)^(1/3) ≥ 0 for positive x, y, z
    replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
        intro x y z hx hy hz
        specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
        -- Handle exponent manipulations
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

    -- Second lemma: For positive x, proves 5/(1+x) + 45/16*(1+x) ≥ 15/2
    -- with equality iff x = 1/3
    have h2 : ∀ x : ℝ, x > 0 → (5 / (1 + x) + 45 / 16 * (1 + x) ≥ 15 / 2) ∧ (5 / (1 + x) + 45 / 16 * (1 + x) = 15 / 2 → x = 1 / 3):= by
      intro x hx
      constructor
      .
        -- Multiply both sides by (1+x) to simplify
        suffices (1 + x) * (5 / (1 + x) + 45 / 16 * (1 + x)) ≥ (1 + x) * (15 / 2) by exact le_of_mul_le_mul_left this (by linarith)
        rw [show (1 + x) * (5 / (1 + x) + 45 / 16 * (1 + x)) = 5 + 45 / 16 * (1 + x) ^ 2 by field_simp ; linarith]
        have g1 : (x - 1 / 3) ^ 2 ≥ 0:= by positivity
        linarith
      .
        intro h
        field_simp at h
        replace h : (x - 1 / 3) ^ 2 = 0:= by linarith
        replace h : x - 1 / 3 = 0:= by exact pow_eq_zero h
        linarith

    -- Rewrite the original expressions to separate terms
    rw [show (7 + 2 * b) / (1 + a) = 5 / (1 + a) + 2 * (1 + b) / (1 + a) by field_simp ; linarith]
    rw [show (7 + 2 * c) / (1 + b) = 5 / (1 + b) + 2 * (1 + c) / (1 + b) by field_simp ; linarith]
    rw [show (7 + 2 * a) / (1 + c) = 5 / (1 + c) + 2 * (1 + a) / (1 + c) by field_simp ; linarith]

    -- Apply lemma h2 to each variable
    have h3:= h2 a ha
    have h4:= h2 b hb
    have h5:= h2 c hc
    rcases h3 with ⟨h3, h3eq⟩
    rcases h4 with ⟨h4, h4eq⟩
    rcases h5 with ⟨h5, h5eq⟩

    -- Apply the transformed Schur's inequality to the ratios
    specialize h1 ((1 + b) / (1 + a)) ((1 + c) / (1 + b)) ((1 + a) / (1 + c)) (by positivity) (by positivity) (by positivity)
    clear h2
    rw [show (1 + b) / (1 + a) * ((1 + c) / (1 + b)) * ((1 + a) / (1 + c)) = 1 by field_simp ; linarith] at h1
    simp at h1
    replace h1 : 6 ≤ 2 * ((1 + b) / (1 + a) + (1 + c) / (1 + b) + (1 + a) / (1 + c)):= by linarith
    rw [show 2 * ((1 + b) / (1 + a) + (1 + c) / (1 + b) + (1 + a) / (1 + c)) = 2 * (1 + b) / (1 + a) + 2 * (1 + c) / (1 + b) + 2 * (1 + a) / (1 + c) by ring] at h1

    -- Combine all inequalities to prove the main statement
    constructor
    .
      linarith only [h1, h3, h4, h5, hab]
    .
      constructor
      .
        -- Prove equality case implies a = b = c = 1/3
        intro h
        replace h3eq:= h3eq (by linarith)
        replace h4eq:= h4eq (by linarith)
        replace h5eq:= h5eq (by linarith)
        clear h3 h4 h5 h1 h
        exact ⟨h3eq, h4eq, h5eq⟩
      .
        -- Prove a = b = c = 1/3 implies equality
        intro h
        rcases h with ⟨g1, g2, g3⟩
        subst a b c
        ring_nf
