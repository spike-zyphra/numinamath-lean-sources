import Mathlib
/- Suppose that there are real numbers $a, b, c \geq 1$ and that there are positive reals $x, y, z$ such that

$$
\begin{aligned}
a^{x}+b^{y}+c^{z} & =4 \\
x a^{x}+y b^{y}+z c^{z} & =6 \\
x^{2} a^{x}+y^{2} b^{y}+z^{2} c^{z} & =9
\end{aligned}
$$

What is the maximum possible value of $c$ ? -/
theorem algebra_608692 : IsGreatest {c : ℝ | ∃ a b x y z : ℝ, a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧ a ^ x + b ^ y + c ^ z = 4 ∧ x * a ^ x + y * b ^ y + z * c ^ z = 6 ∧ x ^ 2 * a ^ x + y ^ 2 * b ^ y + z ^ 2 * c ^ z = 9} ((4 : ℝ) ^ ((1 : ℝ) / 3)):= by
  constructor
  .
    simp
    -- Use a=1 as the first value
    use 1
    simp
    -- Use b=1 as the second value
    use 1
    simp
    constructor
    .
      -- Prove that 4^(1/3) ≥ 1
      field_simp
      have g1 : (4 : ℝ) ≥ 1:= by norm_num
      refine Real.one_le_rpow g1 (by norm_num)
    .
      -- Use x=y=z=3/2 to satisfy the system of equations
      use (3 / 2), (3 / 2), (3 / 2)
      constructor
      .
        -- Prove the first equation: a^x + b^y + c^z = 4
        field_simp
        rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) (3 / 2))]
        ring_nf
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
        rw [Eq.symm (Real.rpow_mul (by positivity) 2 (1 / 2))]
        ring_nf
      .
        constructor
        .
          -- Prove the second equation: x*a^x + y*b^y + z*c^z = 6
          field_simp
          rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) (3 / 2))]
          ring_nf
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
          rw [Eq.symm (Real.rpow_mul (by positivity) 2 (1 / 2))]
          ring_nf
        .
          -- Prove the third equation: x^2*a^x + y^2*b^y + z^2*c^z = 9
          field_simp
          rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) (3 / 2))]
          ring_nf
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
          rw [Eq.symm (Real.rpow_mul (by positivity) 2 (1 / 2))]
          ring_nf
  .
    simp [upperBounds]
    intro c a ha b hb hc x y z h1 h2 h3
    -- Key lemma: For non-zero y1,y2,y3, if (x1^2 + x2^2 + x3^2)(y1^2 + y2^2 + y3^2) = (x1y1 + x2y2 + x3y3)^2
    -- then x1/y1 = x2/y2 = x3/y3 (Cauchy-Schwarz equality condition)
    have h4 : ∀ x1 x2 x3 y1 y2 y3 : ℝ, (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y1 ^ (2 : ℝ) + y2 ^ (2 : ℝ) + y3 ^ (2 : ℝ)) = (x1 * y1 + x2 * y2 + x3 * y3) ^ 2 → y1 ≠ 0 → y2 ≠ 0 → y3 ≠ 0 → x1 / y1 = x2 / y2 ∧ x2 / y2 = x3 / y3:= by
      intro x1 x2 x3 y1 y2 y3 h4 h5 h6 h7
      rw [show y1 ^ (2 : ℝ) = y1 ^ 2 by norm_cast] at h4
      rw [show y2 ^ (2 : ℝ) = y2 ^ 2 by norm_cast] at h4
      rw [show y3 ^ (2 : ℝ) = y3 ^ 2 by norm_cast] at h4
      replace h4 : (x1 * y2 - x2 * y1) ^ 2 + (x1 * y3 - x3 * y1) ^ 2 + (x2 * y3 - x3 * y2) ^ 2 ≤ 0:= by linarith
      have g1 : (x1 * y2 - x2 * y1) ^ 2 + (x1 * y3 - x3 * y1) ^ 2 + (x2 * y3 - x3 * y2) ^ 2 ≥ 0:= by positivity
      replace h4 : (x1 * y2 - x2 * y1) ^ 2 + (x1 * y3 - x3 * y1) ^ 2 + (x2 * y3 - x3 * y2) ^ 2 = 0:= by linarith
      clear g1
      have g1 : (x1 * y2 - x2 * y1) ^ 2 ≥ 0:= by positivity
      have g2 : (x1 * y3 - x3 * y1) ^ 2 ≥ 0:= by positivity
      have g3 : (x2 * y3 - x3 * y2) ^ 2 ≥ 0:= by positivity
      replace g1 :(x1 * y2 - x2 * y1) ^ 2 = 0:= by linarith
      replace g2 :(x1 * y3 - x3 * y1) ^ 2 = 0:= by linarith
      replace g3 :(x2 * y3 - x3 * y2) ^ 2 = 0:= by linarith
      simp at g1 g2 g3
      constructor
      .
        field_simp
        linarith
      .
        field_simp
        linarith
    -- Apply the lemma with carefully chosen values to show x=y=z=3/2
    specialize h4 (x * a ^ (x / 2)) (y * b ^ (y / 2)) (z * c ^ (z / 2)) (a ^ (x / 2)) (b ^ (y / 2)) (c ^ (z / 2)) ?_ ?_ ?_ ?_
    .
      -- Verify the equation condition through algebraic manipulation
      rw [Eq.symm (Real.rpow_mul (by positivity) (x / 2) 2)]
      rw [Eq.symm (Real.rpow_mul (by positivity) (y / 2) 2)]
      rw [Eq.symm (Real.rpow_mul (by positivity) (z / 2) 2)]
      rw [show x * a ^ (x / 2) * a ^ (x / 2) + y * b ^ (y / 2) * b ^ (y / 2) + z * c ^ (z / 2) * c ^ (z / 2) = x * (a ^ (x / 2)) ^ 2 + y * (b ^ (y / 2)) ^ 2 + z * (c ^ (z / 2)) ^ 2 by ring]
      rw [show (a ^ (x / 2)) ^ 2 = (a ^ (x / 2)) ^ (2 : ℝ) by norm_cast]
      rw [show (b ^ (y / 2)) ^ 2 = (b ^ (y / 2)) ^ (2 : ℝ) by norm_cast]
      rw [show (c ^ (z / 2)) ^ 2 = (c ^ (z / 2)) ^ (2 : ℝ) by norm_cast]
      rw [Eq.symm (Real.rpow_mul (by positivity) (x / 2) 2)]
      rw [Eq.symm (Real.rpow_mul (by positivity) (y / 2) 2)]
      rw [Eq.symm (Real.rpow_mul (by positivity) (z / 2) 2)]
      rw [show (x * a ^ (x / 2)) ^ 2 + (y * b ^ (y / 2)) ^ 2 + (z * c ^ (z / 2)) ^ 2 = x ^ 2 * (a ^ (x / 2)) ^ 2 + y ^ 2 * (b ^ (y / 2)) ^ 2 + z ^ 2 * (c ^ (z / 2)) ^ 2 by ring]
      rw [show (a ^ (x / 2)) ^ 2 = (a ^ (x / 2)) ^ (2 : ℝ) by norm_cast]
      rw [show (b ^ (y / 2)) ^ 2 = (b ^ (y / 2)) ^ (2 : ℝ) by norm_cast]
      rw [show (c ^ (z / 2)) ^ 2 = (c ^ (z / 2)) ^ (2 : ℝ) by norm_cast]
      rw [Eq.symm (Real.rpow_mul (by positivity) (x / 2) 2)]
      rw [Eq.symm (Real.rpow_mul (by positivity) (y / 2) 2)]
      rw [Eq.symm (Real.rpow_mul (by positivity) (z / 2) 2)]
      rw [show x / 2 * 2 = x by ring]
      rw [show y / 2 * 2 = y by ring]
      rw [show z / 2 * 2 = z by ring]
      rw [h1, h2, h3]
      linarith
    .
      -- Show all denominators are positive
      positivity
    .
      positivity
    .
      positivity
    .
      -- Use the equality conditions to deduce z = 3/2
      rcases h4 with ⟨h4, h5⟩
      field_simp at h4 h5
      subst x y
      replace h2 : z * 4 = 6:= by rw [←h1] ; linarith
      replace h2 : z = 3 / 2:= by linarith
      subst z
      clear h3
      -- Show that a^(3/2) and b^(3/2) are at least 1
      have h2 : a ^ ((3 : ℝ) / 2) ≥ 1:= by refine Real.one_le_rpow ha (by norm_num)
      have h3 : b ^ ((3 : ℝ) / 2) ≥ 1:= by refine Real.one_le_rpow hb (by norm_num)
      -- Show that c^(3/2) ≤ 2
      replace h1 : c ^ ((3 : ℝ) / 2) ≤ 2:= by linarith
      field_simp
      clear h2 h3
      -- Show that 2 = (4^(1/3))^(3/2)
      have h2 : (2 : ℝ) = (4 ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 2):= by
        rw [Eq.symm (Real.rpow_mul (by positivity) (1 / 3) (3 / 2))]
        ring_nf
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num]
        rw [Eq.symm (Real.rpow_mul (by positivity) 2 (1 / 2))]
        ring_nf
      -- Complete the proof by contradiction
      replace h1 : c ^ ((3 : ℝ) / 2) ≤ (4 ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 2):= by linarith
      clear h2
      by_contra H
      simp at H
      field_simp at H
      -- Final contradiction using properties of real powers
      replace H : c ^ ((3 : ℝ) / 2) > (4 ^ ((1 : ℝ) / 3)) ^ ((3 : ℝ) / 2):= by refine
        (Real.rpow_lt_rpow_iff (by positivity) (by positivity) (by positivity)).mpr H
      linarith
