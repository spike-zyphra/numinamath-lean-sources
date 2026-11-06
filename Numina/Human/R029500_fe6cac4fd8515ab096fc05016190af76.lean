import Mathlib

-- Theorem: For positive real numbers a, b, c where a * b * c = 1,
-- prove that 1/(a³(b+c)) + 1/(b³(a+c)) + 1/(c³(a+b)) ≥ 3/2
theorem algebra_24588 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / (a ^ 3 * (b + c)) + 1 / (b ^ 3 * (a + c)) + 1 / (c ^ 3 * (a + b)) ≥ 3 / 2:= by
  -- Let x = 1/a, y = 1/b, z = 1/c for simpler manipulation
  set x:= 1 / a with hx
  set y:= 1 / b with hy
  set z:= 1 / c with hz
  clear_value x y z

  -- Prove that x * y * z = 1 from the given condition
  have hxyz : x * y * z = 1:= by
    rw [hx, hy, hz]
    field_simp
    rw [h]

  -- Transform the first term using the substitutions
  have g1 : 1 / (a ^ 3 * (b + c)) = x ^ 2 / (y + z):= by
    rw [hx, hy, hz]
    field_simp
    rw [show b * c * (a ^ 3 * (b + c)) = a * b * c * a ^ 2 * (b + c) by ring]
    rw [h]
    linarith

  -- Transform the second term similarly
  have g2 : 1 / (b ^ 3 * (a + c)) = y ^ 2 / (x + z):= by
    rw [hx, hy, hz]
    field_simp
    rw [show a * c * (b ^ 3 * (a + c)) = a * b * c * b ^ 2 * (a + c) by ring]
    rw [h]
    linarith

  -- Transform the third term similarly
  have g3 : 1 / (c ^ 3 * (a + b)) = z ^ 2 / (x + y):= by
    rw [hx, hy, hz]
    field_simp
    rw [show a * b * (c ^ 3 * (a + b)) = a * b * c * c ^ 2 * (a + b) by ring]
    rw [h]
    linarith

  rw [g1, g2, g3]

  -- Prove positivity of x, y, z from original conditions
  replace ha : x > 0:= by
    rw [hx]
    positivity
  replace hb : y > 0:= by
    rw [hy]
    positivity
  replace hc : z > 0:= by
    rw [hz]
    positivity

  -- Key inequality: For positive a,b: a + b ≥ 2√(ab)
  have h1 : ∀ a b : ℝ, a > 0 → b > 0 → a + b ≥ 2 * √ (a * b):= by
    intro a b ha hb
    have h1 : (√a - √b) ^ 2 ≥ 0:= by positivity
    ring_nf at h1
    rw [show √a ^ 2 = a by refine Real.sq_sqrt (by linarith)] at h1
    rw [show √b ^ 2 = b by refine Real.sq_sqrt (by linarith)] at h1
    rw [show √a * √b = √(a * b) by refine Eq.symm (Real.sqrt_mul' a (by linarith))] at h1
    linarith

  -- Inequality for cubic terms
  have h2 : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a ^ 3 + b ^ 3 + c ^ 3 - a * b * c * 3 ≥ 0:= by
    intro a b c ha hb hc
    have h2 : a ^ 3 + b ^ 3 + c ^ 3 - a * b * c * 3 = (a + b + c) / 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2):= by ring_nf
    rw [h2]
    positivity

  -- Property of cube roots
  have h3 : ∀ a : ℝ, a > 0 → (a ^ ((1 : ℝ) / 3)) ^ 3 = a:= by
    intro a ha
    rw [show (a ^ ((1 : ℝ) / 3)) ^ 3 = (a ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) by norm_cast]
    rw [show (a ^ ((1 : ℝ) / 3)) ^ (3 : ℝ) = a ^ (((1 : ℝ) / 3) * 3) by refine Eq.symm (Real.rpow_mul (by linarith) (1 / 3) 3)]
    ring_nf
    simp

  -- Apply inequalities to each term
  have g4 : x ^ 2 / (y + z) + (y + z) / 4 ≥ x:= by
    have g4:= h1 (x ^ 2 / (y + z)) ((y + z) / 4) (by positivity) (by positivity)
    rw [show x ^ 2 / (y + z) * ((y + z) / 4) = x ^ 2 / 4 by field_simp] at g4
    rw [show x ^ 2 / 4 = (x / 2) ^ 2 by ring_nf] at g4
    rw [show √((x / 2) ^ 2) = x / 2 by refine Real.sqrt_sq (by linarith)] at g4
    linarith

  have g5 : y ^ 2 / (x + z) + (x + z) / 4 ≥ y:= by
    have g5:= h1 (y ^ 2 / (x + z)) ((x + z) / 4) (by positivity) (by positivity)
    rw [show y ^ 2 / (x + z) * ((x + z) / 4) = y ^ 2 / 4 by field_simp] at g5
    rw [show y ^ 2 / 4 = (y / 2) ^ 2 by ring_nf] at g5
    rw [show √((y / 2) ^ 2) = y / 2 by refine Real.sqrt_sq (by linarith)] at g5
    linarith

  have g6 : z ^ 2 / (x + y) + (x + y) / 4 ≥ z:= by
    have g6:= h1 (z ^ 2 / (x + y)) ((x + y) / 4) (by positivity) (by positivity)
    rw [show z ^ 2 / (x + y) * ((x + y) / 4) = z ^ 2 / 4 by field_simp] at g6
    rw [show z ^ 2 / 4 = (z / 2) ^ 2 by ring_nf] at g6
    rw [show √((z / 2) ^ 2) = z / 2 by refine Real.sqrt_sq (by linarith)] at g6
    linarith

  -- Final step: prove x + y + z ≥ 3
  have g7 : x + y + z ≥ 3:= by
    have g7:= h2 (x ^ ((1 : ℝ) / 3)) (y ^ ((1 : ℝ) / 3)) (z ^ ((1 : ℝ) / 3)) (by positivity) (by positivity) (by positivity)
    have gx:= h3 x ha
    have gy:= h3 y hb
    have gz:= h3 z hc
    rw [gx, gy, gz] at g7
    rw [show x ^ ((1 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) = (x * y) ^ ((1 : ℝ) / 3) by refine Eq.symm (Real.mul_rpow (by linarith) (by linarith))] at g7
    rw [show (x * y) ^ ((1 : ℝ) / 3) * z ^ ((1 : ℝ) / 3) = (x * y * z) ^ ((1 : ℝ) / 3) by refine Eq.symm (Real.mul_rpow (by positivity) (by linarith))] at g7
    rw [hxyz] at g7
    simp at g7
    linarith
  linarith
