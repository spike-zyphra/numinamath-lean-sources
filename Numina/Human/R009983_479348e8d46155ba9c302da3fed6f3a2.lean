import Mathlib
/-MNE
Let $a, b, c$ be positive real numbers. Prove that
$$
\frac{a}{b}+\sqrt{\frac{b}{c}}+\sqrt[3]{\frac{c}{a}}>2
$$-/
theorem algebra_604717 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / b + (b / c) ^ ((1 : ℝ) / 2) + (c / a) ^ ((1 : ℝ) / 3) > 2 := by
  -- First lemma: For positive reals x, y, z:
  -- x³ + y³ + z³ - 3xyz ≥ 0
  have h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 ≥ 0:= by
    intro x y z hx hy hz
    -- Rewrite using the identity: x³ + y³ + z³ - 3xyz = 1/2(x+y+z)((x-y)² + (y-z)² + (z-x)²)
    have h1 : x ^ 3 + y ^ 3 + z ^ 3 - x * y * z * 3 = 1 / 2 * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) := by ring_nf
    rw [h1]
    positivity

  -- Transform the first lemma using cube roots:
  -- For positive x, y, z: x + y + z - 3(xyz)^(1/3) ≥ 0
  replace h1 : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 → x + y + z - (x * y * z) ^ ((1 : ℝ) / 3) * 3 ≥ 0 := by
    intro x y z hx hy hz
    specialize h1 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
    -- Series of rewrites to handle exponents and simplify
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

  -- Second lemma: For positive x, y:
  -- x + y - 2√(xy) ≥ 0 (AM-GM inequality)
  have h2 : ∀ x y : ℝ, x > 0 → y > 0 → x + y - 2 * √(x * y) ≥ 0 := by
    intro x y hx hy
    have h2 : (√x - √y) ^ 2 ≥ 0 := by positivity
    ring_nf at h2
    rw [show √x * √y = √(x * y) by refine Eq.symm (Real.sqrt_mul' x (by linarith))] at h2
    rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)] at h2
    rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)] at h2
    linarith

  -- Apply first lemma to specific terms
  have g1:= h1 ((b / c) ^ ((1 : ℝ) / 2)) ((b / c) ^ ((1 : ℝ) / 2)) (a / b) (by positivity) (by positivity) (by positivity)
  rw [Eq.symm (Real.rpow_add (by positivity) (1 / 2) (1 / 2))] at g1
  rw [(show (1 : ℝ) / 2 + 1 / 2 = 1 by ring_nf), (show (b / c) ^ (1 : ℝ) = b / c by simp)] at g1

  -- Simplify fraction multiplication
  have g2 : b / c * (a / b) = a / c := by
    field_simp
    ring
  rw [g2] at g1
  clear g2

  -- Apply second lemma to specific terms
  have g2:= h2 ((a / c) ^ ((1 : ℝ) / 3)) ((c / a) ^ ((1 : ℝ) / 3)) (by positivity) (by positivity)
  rw [Eq.symm (Real.mul_rpow (by positivity) (by positivity))] at g2
  rw [show a / c * (c / a) = 1 by field_simp] at g2
  field_simp at g2

  -- Final positivity assertions
  have g3 : a / b > 0:= by positivity
  have g4 : (a / c) ^ ((1 : ℝ) / 3) > 0:= by positivity
  linarith
