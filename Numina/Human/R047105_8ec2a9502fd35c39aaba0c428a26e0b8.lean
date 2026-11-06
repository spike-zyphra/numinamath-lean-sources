import Mathlib
/- Determine all triplets of real numbers $(x, y, z)$ satisfying the system of equations

$$
\begin{aligned}
x^{2} y+y^{2} z & =1040 \\
x^{2} z+z^{2} y & =260 \\
(x-y)(y-z)(z-x) & =-540
\end{aligned}
$$ -/
theorem algebra_610157 : {(x, y, z) : ℝ × ℝ × ℝ | x ^ 2 * y + y ^ 2 * z = 1040 ∧ x ^ 2 * z + z ^ 2 * y = 260 ∧ (x - y) * (y - z) * (z - x) = -540} = {(16, 4, 1), (1, 16, 4)}:= by
  -- We use extensionality to prove equality of sets by showing mutual inclusion
  ext ⟨x, y, z⟩
  constructor
  -- Forward direction: if (x,y,z) satisfies the system, then it equals one of the two points
  .
    intro h
    simp at h
    rcases h with ⟨h1, h2, h3⟩
    -- Derive a new equation from the given ones
    replace h3 : x * y ^ 2 - x * z ^ 2 = 240:= by linarith
    -- Prove that x^2 + y*z ≠ 0 by contradiction
    have g1 : x ^ 2 + y * z ≠ 0:= by
      by_contra H
      replace H : y * (x ^ 2 + y * z) = 0:= by rw [H] ; simp
      linarith
    -- Prove that z ≠ 0 by contradiction
    have g2 : z ≠ 0:= by
      by_contra H
      replace H : z * (x ^ 2 + y * z) = 0:= by rw [H] ; simp
      linarith
    -- Calculate the ratio of the first two equations
    have h4 : (x ^ 2 * y + y ^ 2 * z) / (x ^ 2 * z + z ^ 2 * y) = 1040 / 260:= by rw [h1, h2]
    -- Rewrite the expressions to simplify the ratio
    rw [show x ^ 2 * y + y ^ 2 * z = y * (x ^ 2 + y * z) by ring_nf, show x ^ 2 * z + z ^ 2 * y = z * (x ^ 2 + y * z) by ring] at h4
    -- Simplify the ratio to y/z = 4
    rw [show y * (x ^ 2 + y * z) / (z * (x ^ 2 + y * z)) = y / z by field_simp ; linarith] at h4
    ring_nf at h4
    field_simp at h4
    -- Substitute y = 4*z into the equations
    subst y
    ring_nf at h2
    clear h1
    -- Derive a formula for x in terms of z
    replace h3 : x = 16 / z ^ 2:= by field_simp ; linarith
    subst x
    field_simp at h2
    ring_nf at h2
    -- Obtain a polynomial equation in z
    replace h2 : z * (z ^ 3 - 1) * (z ^ 3 - 64) = 0:= by linarith
    simp [g2] at h2
    -- Split into two cases: z^3 = 1 or z^3 = 64
    rcases h2 with h2 | h2
    -- Case 1: z^3 = 1
    .
      replace h2 : (z - 1) * (z ^ 2 + 1 + (z + 1) ^ 2) = 0:= by linarith
      have g3 : z ^ 2 + 1 + (z + 1) ^ 2 ≠ 0:= by positivity
      simp [g3] at h2
      -- This gives z = 1
      replace h2 : z = 1:= by linarith
      subst z
      ring_nf
      simp
    -- Case 2: z^3 = 64
    .
      replace h2 : (z - 4) * (z ^ 2 + 16 + (z + 4) ^ 2) = 0:= by linarith
      have g3 : z ^ 2 + 16 + (z + 4) ^ 2 ≠ 0:= by positivity
      simp [g3] at h2
      -- This gives z = 4
      replace h2 : z = 4:= by linarith
      subst z
      ring_nf
      simp
  -- Backward direction: verify that both points satisfy the system of equations
  .
    intro h
    simp at h
    rcases h with h | h
    all_goals
      rcases h with ⟨h1, h2, h3⟩
      subst x y z
      simp
      norm_num
