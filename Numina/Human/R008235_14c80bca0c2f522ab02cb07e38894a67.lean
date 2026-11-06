import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a b c=1$. Prove that

$$
\left(a+\frac{1}{b}\right)^{2}+\left(b+\frac{1}{c}\right)^{2}+\left(c+\frac{1}{a}\right)^{2} \geq 3(a+b+c+1)
$$

When does equality hold? -/

-- Main theorem: Proves the inequality and characterizes the equality case (a = b = c = 1)
theorem algebra_605720 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 ≥ 3 * (a + b + c + 1) ∧ ((a + 1 / b) ^ 2 + (b + 1 / c) ^ 2 + (c + 1 / a) ^ 2 = 3 * (a + b + c + 1) ↔ (a = 1 ∧ b = 1 ∧ c = 1)):= by
  -- Lemma 1: For positive reals, proves 3(x² + y² + z²) - (x + y + z)² ≥ 0
  -- This is equivalent to (x-y)² + (y-z)² + (z-x)² ≥ 0
  have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 ≥ 0:= by
    intro x y z _ _ _
    rw [show 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 = (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 by ring_nf]
    positivity
  -- Lemma 2: For positive reals, proves x³ + y³ + z³ - 3xyz ≥ 0 (AM-GM inequality)
  have h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
    intro x y z hx hy hz
    have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
    rw [h1]
    positivity
  -- Transform Lemma 2 using cube roots to get a more useful form
  replace h2 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
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
    simp
    linarith
  -- Apply transformed inequality to original terms (a,b,c)
  have g1:= h2 a b c ha hb hc
  -- Apply transformed inequality to reciprocal terms (1/a, 1/b, 1/c)
  have g2:= h2 (1 / a) (1 / b) (1 / c) (by positivity) (by positivity) (by positivity)
  rw [show (1 / a) * (1 / b) * (1 / c) = 1 / (a * b * c) by field_simp] at g2
  rw [h] at g1 g2
  simp at g1 g2
  -- Apply Lemma 1 to the mixed terms in the original inequality
  have g3:= h1 (a + 1 / b) (b + 1 / c) (c + 1 / a) (by positivity) (by positivity) (by positivity)
  -- Prove sum of mixed terms is greater than sum of original terms plus 3
  have g4 : (a + 1 / b) + (b + 1 / c) + (c + 1 / a) ≥ a + b + c + 3:= by
    simp
    linarith
  replace g4 : ((a + 1 / b) + (b + 1 / c) + (c + 1 / a)) ^ 2 ≥ (a + b + c + 3) ^ 2:= by refine pow_le_pow_left (by linarith) g4 2
  rw [show (a + b + c + 3) ^ 2 = (a + b + c) ^ 2 + 6 * (a + b + c) + 9 by ring_nf] at g4
  have g5 : a + b + c > 0:= by linarith
  replace g5 : (a + b + c) * (a + b + c) ≥ 3 * (a + b + c):= by exact (mul_le_mul_iff_of_pos_right g5).mpr g1
  -- Prove main inequality
  constructor
  .
    linarith
  -- Prove equality case
  .
    constructor
    .
      intro hgoal
      have h3 : (a + 1 / b + (b + 1 / c) + (c + 1 / a)) ^ 2 = (a + b + c) ^ 2 + 6 * (a + b + c) + 9:= by linarith
      have h4 : (a + b + c) * (a + b + c) = 3 * (a + b + c):= by linarith
      rw [show (a + b + c) ^ 2 + 6 * (a + b + c) + 9 = (a + b + c + 3) ^ 2 by ring_nf] at h3
      clear h1 h2 g1 g2 g3 g4 g5
      have g1 : a + 1 / b + (b + 1 / c) + (c + 1 / a) ≥ 0:= by positivity
      have _ : a + b + c + 3 ≥ 0:= by linarith
      have g3 : a + b + c ≠ 0:= by linarith
      replace h4 : (a + b + c - 3) * (a + b + c) = 0:= by linarith
      replace h4 : a + b + c - 3 = 0:= by exact eq_zero_of_ne_zero_of_mul_right_eq_zero g3 h4
      replace h4 : a + b + c = 3:= by linarith
      replace h3 : a + 1 / b + (b + 1 / c) + (c + 1 / a) = a + b + c + 3 ∨ a + 1 / b + (b + 1 / c) + (c + 1 / a) = - (a + b + c + 3):= by exact sq_eq_sq_iff_eq_or_eq_neg.mp h3
      rcases h3 with h3 | h3
      .
        replace h3 : 1 / a + 1 / b + 1 / c = 3:= by linarith
        rw [←h] at h3
        rw [show a * b * c / a = b * c by field_simp ; ring_nf] at h3
        rw [show a * b * c / b = a * c by field_simp ; ring_nf] at h3
        rw [show a * b * c / c = a * b by field_simp] at h3
        have h5 : (a + b + c) ^ 2 = 9:= by rw [h4] ; linarith
        replace h5 : (a + b + c) ^ 2 - 3 * (b * c + a * c + a * b) = 0:= by linarith
        replace h5 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0:= by linarith
        have h6 : (a - b) ^ 2 ≥ 0:= by positivity
        have h7 : (b - c) ^ 2 ≥ 0:= by positivity
        have h8 : (c - a) ^ 2 ≥ 0:= by positivity
        replace h6 : (a - b) ^ 2 = 0:= by linarith
        replace h7 : (b - c) ^ 2 = 0:= by linarith
        replace h6 : a - b = 0:= by exact pow_eq_zero h6
        replace h7 : b - c = 0:= by exact pow_eq_zero h7
        refine ⟨?_, ?_, ?_⟩
        all_goals
        linarith
      .
        by_contra _
        linarith
    .
      intro ⟨ga, gb, gc⟩
      rw [ga, gb, gc]
      linarith
