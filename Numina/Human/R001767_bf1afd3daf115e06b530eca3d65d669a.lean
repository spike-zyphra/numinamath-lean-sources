import Mathlib

open Real

/-Let $x$, $y$ and $z$ be positive real numbers such that $\sqrt{xy} + \sqrt{yz} + \sqrt{zx} = 3$. Prove that 
$\sqrt{x^3+x} + \sqrt{y^3+y} + \sqrt{z^3+z} \geq \sqrt{6(x+y+z)}$-/
theorem inequalities_33402 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : sqrt (x * y) + sqrt (y * z) + sqrt (z * x) = 3) :
    sqrt (x ^ 3 + x) + sqrt (y ^ 3 + y) + sqrt (z ^ 3 + z) ≥ sqrt (6 * (x + y + z)) := by
  -- For each variable \(a \in \{x, y, z\}\):
  -- $ a^3 + a \geq 2a^2 \quad \text{(by AM-GM: } \frac{a^3 + a}{2} \geq \sqrt{a^3 \cdot a} = a^2\text{)} $
  -- Taking the square root of both sides:
  -- $ sqrt{a^3 + a} \geq \sqrt{2a^2} = a\sqrt{2} $
  have h1 : sqrt (x ^ 3 + x) ≥ sqrt 2 * x := by
    have h2 : x ^ 3 + x ≥ 2 * x ^ 2 := by
      nlinarith [sq_nonneg (x - 1)]

    have h3 : sqrt (x ^ 3 + x) ≥ sqrt (2 * x ^ 2) := by
      apply sqrt_le_sqrt
      linarith

    have h4 : sqrt (2 * x ^ 2) = sqrt 2 * x := by
      rw [show (2 * x ^ 2 : ℝ) = (2 : ℝ) * (x ^ 2 : ℝ) by ring]
      rw [sqrt_mul (by linarith)]
      rw [show (x ^ 2 : ℝ) = (x : ℝ) ^ 2 by ring]
      rw [sqrt_sq (by linarith)]

    linarith

  have h2 : sqrt (y ^ 3 + y) ≥ sqrt 2 * y := by
    have h3 : y ^ 3 + y ≥ 2 * y ^ 2 := by
      nlinarith [sq_nonneg (y - 1)]

    have h4 : sqrt (y ^ 3 + y) ≥ sqrt (2 * y ^ 2) := by
      apply sqrt_le_sqrt
      linarith

    have h5 : sqrt (2 * y ^ 2) = sqrt 2 * y := by
      rw [show (2 * y ^ 2 : ℝ) = (2 : ℝ) * (y ^ 2 : ℝ) by ring]
      rw [sqrt_mul (by linarith)]
      rw [show (y ^ 2 : ℝ) = (y : ℝ) ^ 2 by ring]
      rw [sqrt_sq (by linarith)]

    linarith

  have h3 : sqrt (z ^ 3 + z) ≥ sqrt 2 * z := by
    have h4 : z ^ 3 + z ≥ 2 * z ^ 2 := by
      nlinarith [sq_nonneg (z - 1)]

    have h5 : sqrt (z ^ 3 + z) ≥ sqrt (2 * z ^ 2) := by
      apply sqrt_le_sqrt
      linarith

    have h6 : sqrt (2 * z ^ 2) = sqrt 2 * z := by
      rw [show (2 * z ^ 2 : ℝ) = (2 : ℝ) * (z ^ 2 : ℝ) by ring]
      rw [sqrt_mul (by linarith)]
      rw [show (z ^ 2 : ℝ) = (z : ℝ) ^ 2 by ring]
      rw [sqrt_sq (by linarith)]

    linarith

  have h4 : sqrt (x ^ 3 + x) + sqrt (y ^ 3 + y) + sqrt (z ^ 3 + z) ≥ sqrt 2 * (x + y + z) := by
    linarith [h1, h2, h3]
  
  -- Establish that $\(x + y + z \geq 3\)$
  have h5 : x + y + z ≥ 3 := by
    -- Using the AM-GM inequality
    have h6 : sqrt (x * y) ≤ (x + y) / 2 := by
      have h7 : (x * y) ≤ ((x + y) / 2) ^ 2 := by
        nlinarith [sq_nonneg (x - y)]

      have h8 : sqrt (x * y) ≤ sqrt (((x + y) / 2) ^ 2) := by
        apply sqrt_le_sqrt
        linarith

      have h9 : sqrt (((x + y) / 2) ^ 2) = (x + y) / 2 := by
        rw [Real.sqrt_sq]
        linarith

      linarith

    have h7 : sqrt (y * z) ≤ (y + z) / 2 := by
      have h8 : (y * z) ≤ ((y + z) / 2) ^ 2 := by
        nlinarith [sq_nonneg (y - z)]

      have h9 : sqrt (y * z) ≤ sqrt (((y + z) / 2) ^ 2) := by
        apply sqrt_le_sqrt
        linarith

      have h10 : sqrt (((y + z) / 2) ^ 2) = (y + z) / 2 := by
        rw [Real.sqrt_sq]
        linarith

      linarith

    have h8 : sqrt (z * x) ≤ (z + x) / 2 := by
      have h9 : (z * x) ≤ ((z + x) / 2) ^ 2 := by
        nlinarith [sq_nonneg (z - x)]

      have h10 : sqrt (z * x) ≤ sqrt (((z + x) / 2) ^ 2) := by
        apply sqrt_le_sqrt
        linarith

      have h11 : sqrt (((z + x) / 2) ^ 2) = (z + x) / 2 := by
        rw [Real.sqrt_sq]
        linarith

      linarith
    -- Summing these inequalities:
    have h9 : sqrt (x * y) + sqrt (y * z) + sqrt (z * x) ≤ (x + y + z) := by
      linarith [h6, h7, h8]

    linarith [h, h9]

  have h6 : sqrt 2 * (x + y + z) ≥ sqrt (6 * (x + y + z)) := by
    -- We need to show:$\sqrt{2}(x + y + z) \geq \sqrt{6(x + y + z)}$
    --Square both sides to eliminate the square roots:$2(x + y + z)^2 \geq 6(x + y + z)$
    have h7 : 6 * (x + y + z) ≤ (sqrt 2 * (x + y + z)) ^ 2 := by
      have h8 : (sqrt 2 * (x + y + z)) ^ 2 = (sqrt 2) ^ 2 * (x + y + z) ^ 2 := by ring
      rw [h8]
      have h9 : (sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      rw [h9]
      nlinarith [sq_nonneg (x + y + z), h5]

    have h10 : sqrt (6 * (x + y + z)) ≥ 0 := by
      apply sqrt_nonneg

    have h11 : sqrt 2 * (x + y + z) ≥ 0 := by
      apply mul_nonneg
      · apply sqrt_nonneg
      · linarith

    have h12 : sqrt (6 * (x + y + z)) ≤ sqrt 2 * (x + y + z) := by
      have h13 : (sqrt (6 * (x + y + z))) ^ 2 ≤ (sqrt 2 * (x + y + z)) ^ 2 := by nlinarith [h7, Real.sq_sqrt (show 0 ≤ 6 * (x + y + z) by nlinarith [h5]), sq_nonneg (sqrt 2 * (x + y + z))]
      have h14 : sqrt (6 * (x + y + z)) ≥ 0 := by
        apply sqrt_nonneg
      have h15 : sqrt 2 * (x + y + z) ≥ 0 := by
        apply mul_nonneg
        · apply sqrt_nonneg
        · linarith
      nlinarith [h13, Real.sqrt_nonneg (6 * (x + y + z)), h14, h15]

    linarith [h12]

  linarith [h4, h6]