import Mathlib
set_option maxHeartbeats 400000
/- 7. If $x, y, z$ are three positive numbers, prove: $\sqrt{3}\left(\frac{y z}{x}+\frac{z x}{y}+\frac{x y}{z}\right) \geqslant(y z+z x+x y)$ $\sqrt{\frac{x+y+z}{x y z}}$, and the equality holds if and only if $x=y=z$. (Mathematical Bulletin Problem 444) -/
theorem number_theory_597395 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : √3 * (y * z / x + z * x / y + x * y / z) ≥ (y * z + z * x + x * y) * √((x + y + z) / (x * y * z)) ∧ (√3 * (y * z / x + z * x / y + x * y / z) = (y * z + z * x + x * y) * √((x + y + z) / (x * y * z)) ↔ (x = y ∧ y = z)):= by
  constructor
  -- First part: proving the inequality
  .
    -- Convert expressions to their absolute values (which doesn't change them since they're positive)
    rw [show √3 * (y * z / x + z * x / y + x * y / z) = |√3 * (y * z / x + z * x / y + x * y / z)| by exact Eq.symm (abs_of_pos (by positivity))]
    rw [show (y * z + z * x + x * y) * √((x + y + z) / (x * y * z)) = |(y * z + z * x + x * y) * √((x + y + z) / (x * y * z))| by exact Eq.symm (abs_of_pos (by positivity))]

    -- Use the fact that a ≥ b iff a² ≥ b² for positive numbers
    suffices (√3 * (y * z / x + z * x / y + x * y / z)) ^ 2 ≥ ((y * z + z * x + x * y) * √((x + y + z) / (x * y * z))) ^ 2 by exact sq_le_sq.mp this

    -- Simplify the left side of the inequality
    rw [show (√3 * (y * z / x + z * x / y + x * y / z)) ^ 2 =  3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 / (x ^ 2 * y ^ 2 * z ^ 2) by ring_nf ; field_simp ; ring_nf]

    -- Simplify the right side of the inequality
    rw [show ((y * z + z * x + x * y) * √((x + y + z) / (x * y * z))) ^ 2 = (y * z + z * x + x * y) ^ 2 * ((x + y + z) / (x * y * z)) by set t:= (x + y + z) / (x * y * z) with ht ; clear_value t ; ring_nf ; field_simp [show t ≥ 0 by subst t ; positivity]]

    -- Establish that x²y²z² > 0 for use in the division inequality
    have h : x ^ 2 * y ^ 2 * z ^ 2 > 0:= by positivity

    -- Multiply both sides by x²y²z² to eliminate the division
    suffices 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 ≥ (y * z + z * x + x * y) ^ 2 * ((x + y + z) / (x * y * z)) * (x ^ 2 * y ^ 2 * z ^ 2) by exact (le_div_iff₀ h).mpr this

    -- Further simplify the right side
    rw [show (y * z + z * x + x * y) ^ 2 * ((x + y + z) / (x * y * z)) * (x ^ 2 * y ^ 2 * z ^ 2) = (y * z + z * x + x * y) ^ 2 * ((x + y + z) * (x * y * z)) by field_simp ; ring_nf]

    -- Rewrite the left side
    rw [show 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 = 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) by ring]

    -- Prove the first key inequality
    have h1 : 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ≥ (y * z + z * x + x * y) ^ 2:= by
      have h1 : z ^ 2 * (x - y) ^ 2 + x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2 ≥ 0:= by positivity
      linarith

    -- Prove the second key inequality
    have h2 : y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 ≥ (x + y + z) * (x * y * z):= by linarith

    -- Combine the two inequalities using the fact that multiplying inequalities with positive terms preserves the inequality
    refine mul_le_mul_of_nonneg h1 h2 (by positivity) (by positivity)

  -- Second part: proving the equality condition (iff x = y = z)
  .
    constructor
    -- Forward direction: if equality holds, then x = y = z
    .
      intro h
      -- Square both sides of the equality
      replace h : (√3 * (y * z / x + z * x / y + x * y / z)) ^ 2 = ((y * z + z * x + x * y) * √((x + y + z) / (x * y * z))) ^ 2:= by rw [h]

      -- Simplify the left side
      rw [show (√3 * (y * z / x + z * x / y + x * y / z)) ^ 2 =  3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 / (x ^ 2 * y ^ 2 * z ^ 2) by ring_nf ; field_simp ; ring_nf] at h

      -- Simplify the right side
      rw [show ((y * z + z * x + x * y) * √((x + y + z) / (x * y * z))) ^ 2 = (y * z + z * x + x * y) ^ 2 * ((x + y + z) / (x * y * z)) by set t:= (x + y + z) / (x * y * z) with ht ; clear_value t ; ring_nf ; field_simp [show t ≥ 0 by subst t ; positivity]] at h

      -- Multiply both sides by x²y²z²
      replace h : 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 / (x ^ 2 * y ^ 2 * z ^ 2) * (x ^ 2 * y ^ 2 * z ^ 2) =
      (y * z + z * x + x * y) ^ 2 * ((x + y + z) / (x * y * z)) * (x ^ 2 * y ^ 2 * z ^ 2):= by rw [h]

      -- Simplify both sides after multiplication
      rw [show 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 / (x ^ 2 * y ^ 2 * z ^ 2) * (x ^ 2 * y ^ 2 * z ^ 2) = 3 * (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2) ^ 2 by field_simp] at h
      rw [show (y * z + z * x + x * y) ^ 2 * ((x + y + z) / (x * y * z)) * (x ^ 2 * y ^ 2 * z ^ 2) = (y * z + z * x + x * y) ^ 2 * ((x + y + z) * (x * y * z)) by field_simp ; ring_nf] at h

      -- Algebraic manipulation to isolate the terms with (x-y)², (y-z)², (z-x)²
      replace h : (y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 + 1 / 2 * ((y * z + z * x + x * y) ^ 2)) * (z ^ 2 * (x - y) ^ 2 + x ^ 2 * (y - z) ^ 2 + y ^ 2 * (z - x) ^ 2) = 0:= by linarith only [h]

      -- Define a temporary variable for the first factor
      set t:= y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 + 1 / 2 * ((y * z + z * x + x * y) ^ 2) with ht
      clear_value t

      -- Prove that the first factor is non-zero
      replace ht : t ≠ 0:= by subst t ; positivity
      simp [ht] at h

      -- Establish that each squared term is non-negative
      have g1 : z ^ 2 * (x - y) ^ 2 ≥ 0:= by positivity
      have g2 : x ^ 2 * (y - z) ^ 2 ≥ 0:= by positivity
      have g3 : y ^ 2 * (z - x) ^ 2 ≥ 0:= by positivity

      -- Since their sum is zero and each term is non-negative, each term must be zero
      replace g1 : z ^ 2 * (x - y) ^ 2 = 0:= by linarith
      replace g2 : x ^ 2 * (y - z) ^ 2 = 0:= by linarith

      -- Since x, z ≠ 0, we must have x = y and y = z
      simp [show x ≠ 0 by linarith, show z ≠ 0 by linarith] at g1 g2

      -- Conclude that x = y and y = z
      constructor
      all_goals
        linarith

    -- Reverse direction: if x = y = z, then equality holds
    .
      intro h
      rcases h with ⟨h1, h2⟩
      subst x y
      field_simp
      ring_nf
      field_simp
      ring_nf
