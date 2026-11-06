import Mathlib
/- Let $a, b, c$ be the side lengths of a triangle. Prove that

$$
\sqrt[3]{\left(a^{2}+b c\right)\left(b^{2}+c a\right)\left(c^{2}+a b\right)}>\frac{a^{2}+b^{2}+c^{2}}{2} .
$$ -/
theorem algebra_604521 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h1 : a + b > c) (h2 : a + c > b) (h3 : b + c > a) :
  ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) ^ ((1 : ℝ) / 3) >
  (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
    -- First prove that a² + bc > (a² + b² + c²)/2
    -- This is done by showing a > |b-c| using triangle inequality
    have h4 : a ^ 2 + b * c > (a ^ 2 + b ^ 2 + c ^ 2) / 2:= by
      suffices a ^ 2 > (b - c) ^ 2 by linarith
      suffices |a| > |b - c| by exact sq_lt_sq.mpr this
      rw [show |a| = a by exact abs_of_pos ha]
      suffices a > b - c ∧ a > c - b by exact abs_sub_lt_iff.mpr this
      constructor
      all_goals
      linarith

    -- Similarly prove that b² + ca > (a² + b² + c²)/2
    have h5 : b ^ 2 + c * a > (a ^ 2 + b ^ 2 + c ^ 2) / 2:= by
      suffices b ^ 2 > (c - a) ^ 2 by linarith
      suffices |b| > |c - a| by exact sq_lt_sq.mpr this
      rw [show |b| = b by exact abs_of_pos hb]
      suffices b > c - a ∧ b > a - c by exact abs_sub_lt_iff.mpr this
      constructor
      all_goals
      linarith

    -- And prove that c² + ab > (a² + b² + c²)/2
    have h6 : c ^ 2 + a * b > (a ^ 2 + b ^ 2 + c ^ 2) / 2:= by
      suffices c ^ 2 > (a - b) ^ 2 by linarith
      suffices |c| > |a - b| by exact sq_lt_sq.mpr this
      rw [show |c| = c by exact abs_of_pos hc]
      suffices c > a - b ∧ c > b - a by exact abs_sub_lt_iff.mpr this
      constructor
      all_goals
      linarith

    -- Prove (a² + b² + c²)/2 > 0
    have h7 : (a ^ 2 + b ^ 2 + c ^ 2) / 2 > 0:= by positivity

    -- Use multiplication of inequalities to build up the final result
    have h8 : (a ^ 2 + b * c) * (b ^ 2 + c * a) > ((a ^ 2 + b ^ 2 + c ^ 2) / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / 2):= by refine mul_lt_mul_of_pos_of_nonneg' h4 (by linarith) h7 (by linarith)
    replace h7 : ((a ^ 2 + b ^ 2 + c ^ 2) / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / 2) > 0:= by positivity
    replace h8 : (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) > ((a ^ 2 + b ^ 2 + c ^ 2) / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / 2):= by refine mul_lt_mul_of_pos_of_nonneg' h8 (by linarith) (by positivity) (by linarith)

    -- Clean up unused hypotheses
    clear h1 h2 h3 h4 h5 h6 h7

    -- Final algebraic manipulations to get the cube root form
    rw [show ((a ^ 2 + b ^ 2 + c ^ 2) / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / 2) * ((a ^ 2 + b ^ 2 + c ^ 2) / 2) = ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 by ring] at h8
    replace h8 : ((a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) ^ ((1 : ℝ) / 3) > (((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3) ^ ((1 : ℝ) / 3):= by refine Real.rpow_lt_rpow (by positivity) h8 (by positivity)
    rw [show ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ 3 = ((a ^ 2 + b ^ 2 + c ^ 2) / 2) ^ (3 : ℝ) by norm_cast] at h8
    rw [Eq.symm (Real.rpow_mul (by positivity) 3 (1 / 3))] at h8
    rw [show (3 : ℝ) * (1 / 3) = 1 by ring_nf] at h8
    simp at h8
    simp
    linarith
