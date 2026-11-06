import Mathlib
open Real
/- 3. Let $x, y, z$ be positive real numbers such that $x y z=1$. Prove that

$$
\frac{x^{2}+y^{2}+z}{x^{2}+2}+\frac{y^{2}+z^{2}+x}{y^{2}+2}+\frac{z^{2}+x^{2}+y}{z^{2}+2} \geq 3
$$

When does equality hold? -/
theorem inequalities_234334 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 1) :
3 ≤ (x ^ 2 + y ^ 2 + z) / (x ^ 2 + 2) + (y ^ 2 + z ^ 2 + x) / (y ^ 2 + 2) + (z ^ 2 + x ^ 2 + y) / (z ^ 2 + 2) ∧
(3 = (x ^ 2 + y ^ 2 + z) / (x ^ 2 + 2) + (y ^ 2 + z ^ 2 + x) / (y ^ 2 + 2) + (z ^ 2 + x ^ 2 + y) / (z ^ 2 + 2) ↔ x = 1 ∧ y = 1 ∧ z = 1):= by
  -- Rewrite each fraction by extracting a perfect square term
  have g1 : (x ^ 2 + y ^ 2 + z) / (x ^ 2 + 2) = (x - y) ^ 2 / (x ^ 2 + 2) + (2 * x * y + z) / (x ^ 2 + 2):= by field_simp ; linarith
  have g2 : (y ^ 2 + z ^ 2 + x) / (y ^ 2 + 2) = (y - z) ^ 2 / (y ^ 2 + 2) + (2 * y * z + x) / (y ^ 2 + 2):= by field_simp ; linarith
  have g3 : (z ^ 2 + x ^ 2 + y) / (z ^ 2 + 2) = (z - x) ^ 2 / (z ^ 2 + 2) + (2 * z * x + y) / (z ^ 2 + 2):= by field_simp ; linarith

  -- Establish that the square terms are non-negative
  have g4 : (x - y) ^ 2 / (x ^ 2 + 2) ≥ 0:= by positivity
  have g5 : (y - z) ^ 2 / (y ^ 2 + 2) ≥ 0:= by positivity
  have g6 : (z - x) ^ 2 / (z ^ 2 + 2) ≥ 0:= by positivity

  -- Rewrite the remaining terms using algebraic manipulations
  rw [show (2 * x * y + z) / (x ^ 2 + 2) = (2 * x * y * z + z ^ 2) / (z * (x ^ 2 + 2)) by field_simp ; linarith] at g1
  rw [show (2 * y * z + x) / (y ^ 2 + 2) = (2 * x * y * z + x ^ 2) / (x * (y ^ 2 + 2)) by field_simp ; linarith] at g2
  rw [show (2 * z * x + y) / (z ^ 2 + 2) = (2 * x * y * z + y ^ 2) / (y * (z ^ 2 + 2)) by field_simp ; linarith] at g3

  -- Use the constraint x*y*z = 1 to simplify
  rw [show 2 * x * y * z = 2 by linarith] at g1 g2 g3

  -- Establish a key inequality for the AM-GM relationship
  have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
    intro x y z hx hy hz
    -- Express the inequality in terms of squared differences
    have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
    rw [h1]
    positivity

  -- Generalize the inequality using cube roots
  replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
    intro x y z hx hy hz
    specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
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

  -- Apply the inequality to our specific terms
  specialize h1 ((2 + z ^ 2) / (z * (x ^ 2 + 2))) ((2 + x ^ 2) / (x * (y ^ 2 + 2))) ((2 + y ^ 2) / (y * (z ^ 2 + 2))) (by positivity) (by positivity) (by positivity)
  rw [show (2 + z ^ 2) / (z * (x ^ 2 + 2)) * ((2 + x ^ 2) / (x * (y ^ 2 + 2))) * ((2 + y ^ 2) / (y * (z ^ 2 + 2))) = 1 / (x * y * z) by field_simp ; linarith] at h1
  rw [hxyz] at h1
  simp at h1

  -- Construct the final proof with two parts: inequality and equality condition
  constructor
  -- Prove the inequality
  .
    linarith
  -- Characterize when equality holds
  .
    constructor
    -- Forward direction: if equality holds, then x = y = z = 1
    .
      intro h
      replace g4 : (x - y) ^ 2 / (x ^ 2 + 2) = 0:= by linarith
      replace g5 : (y - z) ^ 2 / (y ^ 2 + 2) = 0:= by linarith
      have g7 : x ^ 2 + 2 ≠ 0:= by positivity
      have g8 : y ^ 2 + 2 ≠ 0:= by positivity
      simp [g7, g8] at g4 g5
      replace g4 : x = y:= by linarith
      replace g5 : y = z:= by linarith
      subst x y
      replace hxyz : (z - 1) * ((2 * z + 1) ^ 2 + 3) = 0:= by linarith
      have gxyz : (2 * z + 1) ^ 2 + 3 ≠ 0:= by positivity
      simp [gxyz] at hxyz
      replace hxyz : z = 1:= by linarith
      subst z
      simp
    -- Reverse direction: if x = y = z = 1, then equality holds
    .
      rintro ⟨rfl, rfl, rfl⟩
      norm_num
