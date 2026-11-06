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

  have h1 : x * y * z = 1 := hxyz
  clear hxyz

  have h2 : x ^ 2 / (y + z) + y ^ 2 / (x + z) + z ^ 2 / (x + y) - 3 / 2 ≥ 0:= by
    have h2 : (y + z) * (x + z) * (x + y) > 0:= by positivity
    have h3 : x ^ 2 / (y + z) + y ^ 2 / (x + z) + z ^ 2 / (x + y) - 3 / 2 =
      (2 * x ^ 2 * (x + z) * (x + y) + 2 * y ^ 2 * (y + z) * (y + x) + 2 * z ^ 2 * (z + x) * (z + y) - 3 * (y + z) * (x + z) * (x + y)) / (2 * (y + z) * (x + z) * (x + y)):= by 
        field_simp
        ring_nf
    rw [h3]
    suffices 2 * x ^ 2 * (x + z) * (x + y) + 2 * y ^ 2 * (y + z) * (y + x) + 2 * z ^ 2 * (z + x) * (z + y) - 3 * (y + z) * (x + z) * (x + y) ≥ 0 by 
      apply div_nonneg
      linarith
      positivity
    nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
      h1,  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  linarith