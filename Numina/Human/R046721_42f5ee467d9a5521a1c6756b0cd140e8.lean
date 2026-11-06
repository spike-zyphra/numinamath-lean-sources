import Mathlib
/- Example 9 Let $a, b, c \in \mathbf{R}^{+}$, and $a b c=1$, find the maximum value of $\frac{1}{a+b+1}+\frac{1}{b+c+1}+\frac{1}{c+a+1}$. -/
theorem inequalities_175760 : IsGreatest {S : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a * b * c = 1 ∧ S = 1 / (a + b + 1) + 1 / (b + c + 1) + 1 / (c + a + 1)} 1:= by
  constructor
  -- First part: Prove that 1 is in the set (i.e., the value 1 is achievable)
  .
    simp
    use 1
    simp
    use 1
    simp
    use 1
    simp
    norm_num
  -- Second part: Prove that 1 is an upper bound for all values in the set
  .
    simp [upperBounds]
    intro S a ha b hb c hc h hS
    subst S
    -- Apply the AM-GM substitution technique by setting new variables
    set x:= a ^ ((1 : ℝ) / 3) with hx
    set y:= b ^ ((1 : ℝ) / 3) with hy
    set z:= c ^ ((1 : ℝ) / 3) with hz
    clear_value x y z
    -- Prove that x, y, z are positive
    have hxpos : x > 0:= by subst x ; positivity
    have hypos : y > 0:= by subst y ; positivity
    have hzpos : z > 0:= by subst z ; positivity
    -- Establish the relationship between x^3 and a
    replace hx : x ^ 3 = a:= by
      rw [show x ^ 3 = x ^ (3 : ℝ) by norm_cast]
      subst x
      rw [←(Real.rpow_mul (by positivity) (1 / 3) 3)]
      simp
    -- Establish the relationship between y^3 and b
    replace hy : y ^ 3 = b:= by
      rw [show y ^ 3 = y ^ (3 : ℝ) by norm_cast]
      subst y
      rw [←(Real.rpow_mul (by positivity) (1 / 3) 3)]
      simp
    -- Establish the relationship between z^3 and c
    replace hz : z ^ 3 = c:= by
      rw [show z ^ 3 = z ^ (3 : ℝ) by norm_cast]
      subst z
      rw [←(Real.rpow_mul (by positivity) (1 / 3) 3)]
      simp
    -- Prove that x*y*z = 1 from the constraint a*b*c = 1
    have h1 : x * y * z = 1:= by
      rw [←hx, ←hy, ←hz] at h
      replace h : (x * y * z - 1) * ((2 * x * y * z + 1) ^ 2 + 3) = 0:= by linarith
      have g1 : (2 * x * y * z + 1) ^ 2 + 3 ≠ 0:= by positivity
      simp [g1] at h
      linarith
    -- Rewrite the expression in terms of x, y, z
    rw [←hx, ←hy, ←hz]
    clear ha hb hc h hx hy hz a b c
    -- Convert reciprocals to division form for clarity
    rw [show (x ^ 3 + y ^ 3 + 1)⁻¹ = 1 / (x ^ 3 + y ^ 3 + 1) by field_simp]
    rw [show (y ^ 3 + z ^ 3 + 1)⁻¹ = 1 / (y ^ 3 + z ^ 3 + 1) by field_simp]
    rw [show (z ^ 3 + x ^ 3 + 1)⁻¹ = 1 / (z ^ 3 + x ^ 3 + 1) by field_simp]
    -- Apply inequality: x^3 + y^3 + 1 ≥ x^2*y + x*y^2 + 1
    have g1 : x ^ 3 + y ^ 3 + 1 ≥ x ^ 2 * y + x * y ^ 2 + 1:= by
      suffices (x + y) * (x - y) ^ 2 ≥ 0 by linarith
      positivity
    -- Apply inequality: y^3 + z^3 + 1 ≥ y^2*z + y*z^2 + 1
    have g2 : y ^ 3 + z ^ 3 + 1 ≥ y ^ 2 * z + y * z ^ 2 + 1:= by
      suffices (y + z) * (y - z) ^ 2 ≥ 0 by linarith
      positivity
    -- Apply inequality: z^3 + x^3 + 1 ≥ z^2*x + z*x^2 + 1
    have g3 : z ^ 3 + x ^ 3 + 1 ≥ z ^ 2 * x + z * x ^ 2 + 1:= by
      suffices (z + x) * (z - x) ^ 2 ≥ 0 by linarith
      positivity
    -- Apply the fact that 1/a ≤ 1/b if a ≥ b > 0
    replace g1:= one_div_le_one_div_of_le (by positivity) g1
    replace g2:= one_div_le_one_div_of_le (by positivity) g2
    replace g3:= one_div_le_one_div_of_le (by positivity) g3
    -- Simplify the expressions using the constraint x*y*z = 1
    rw [show 1 / (x ^ 2 * y + x * y ^ 2 + 1) = z / (x + y + z) by rw [←h1] ; field_simp ; ring_nf] at g1
    rw [show 1 / (y ^ 2 * z + y * z ^ 2 + 1) = x / (x + y + z) by rw [←h1] ; field_simp ; ring_nf] at g2
    rw [show 1 / (z ^ 2 * x + z * x ^ 2 + 1) = y / (x + y + z) by rw [←h1] ; field_simp ; ring_nf] at g3
    -- Prove that the sum of the three fractions equals 1
    have g4 : z / (x + y + z) + x / (x + y + z) + y / (x + y + z) = 1:= by field_simp ; ring_nf
    -- Complete the proof using linear arithmetic
    linarith
