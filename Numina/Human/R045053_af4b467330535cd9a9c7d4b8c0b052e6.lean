import Mathlib
/- Let $S=T_{5}$. Given real numbers $a, b, c$ such that $a^{2}+b^{2}+c^{2}+(a+b+c)^{2}=S$, find the maximum possible value of $(a+b)(b+c)(c+a)$. -/
theorem algebra_610028 : IsGreatest {x : ℝ | ∃ a b c : ℝ, a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 = 27 ∧ x = (a + b) * (b + c) * (c + a)} 27:= by
  constructor
  -- Part 1: Prove that 27 is achievable with a = b = c = 3/2
  .
    simp
    use (3 / 2)
    use (3 / 2)
    use (3 / 2)
    ring_nf
    simp
  -- Part 2: Prove that 27 is the maximum value
  .
    simp [upperBounds]
    intro x a b c h h2
    subst x
    -- Lemma 1: For any non-negative real numbers x, y, z: x^3 + y^3 + z^3 - 3xyz ≥ 0
    have h1 : ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
      intro x y z hx hy hz
      -- Express the inequality using squares of differences
      have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
      rw [h1]
      positivity
    -- Lemma 2: For any non-negative real numbers x, y, z: x + y + z - 3(xyz)^(1/3) ≥ 0
    replace h1 : ∀ x y z : ℝ, x ≥ 0 → y ≥ 0 → z ≥ 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
      intro x y z hx hy hz
      specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
      -- Series of algebraic manipulations to transform the expression
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
    -- Apply the lemma to squares of sums
    rw [show a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 = (a + b) ^ 2 + (b + c) ^ 2 + (c + a) ^ 2 by linarith] at h
    specialize h1 ((a + b) ^ 2) ((b + c) ^ 2) ((c + a) ^ 2) (by positivity) (by positivity) (by positivity)
    rw [h] at h1
    clear h
    -- Final steps of the proof using contradiction
    rw [show (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 = ((a + b) * (b + c) * (c + a)) ^ 2 by ring_nf] at h1
    replace h1 : (((a + b) * (b + c) * (c + a)) ^ 2) ^ ((1 : ℝ) / 3) ≤ 9:= by linarith
    by_contra H
    simp at H
    replace H : ((a + b) * (b + c) * (c + a)) ^ 2 > 27 ^ 2:= by nlinarith only [H]
    have g1 : (27 : ℝ) ^ 2 ≥ 0:= by positivity
    have g2 : ((a + b) * (b + c) * (c + a)) ^ 2 ≥ 0:= by positivity
    replace H : (((a + b) * (b + c) * (c + a)) ^ 2) ^ ((1 : ℝ) / 3) > (27 ^ 2) ^ ((1 : ℝ) / 3):= by refine (Real.rpow_lt_rpow_iff g1 g2 (by linarith)).mpr H
    rw [show (27 : ℝ) ^ 2 = 9 ^ (3 : ℝ) by ring_nf] at H
    rw [Eq.symm (Real.rpow_mul (by linarith) 3 (1 / 3))] at H
    rw [show (3 : ℝ) * (1 / 3) = 1 by ring_nf] at H
    simp at H h1
    linarith
