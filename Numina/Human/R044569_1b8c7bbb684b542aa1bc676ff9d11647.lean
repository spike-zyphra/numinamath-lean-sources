import Mathlib

/- Let $a, b, c, d$ be four real numbers such that $a \geqslant b \geqslant c \geqslant d>0$ and $a+b+c+d=1$. Prove that  $$ (a+2 b+3 c+4 d) a^{a} b^{b} c^{c} d^{d}<1 $$  (Belgium) -/
theorem Algebra_a4 {a b c d : ℝ} (hdpos : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (h : a + b + c + d = 1) :
    (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 := by
  -- We have a, b, c, d > 0
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hcpos : 0 < c := by linarith
  have hdpos : 0 < d := by linarith
  -- We have a ^ a * b ^ b * c ^ c * d ^ d ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2
  have h₀ : a ^ a * b ^ b * c ^ c * d ^ d ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
    -- Apply the weighted AM-GM inequality
    have h₀ := Real.geom_mean_le_arith_mean_weighted Finset.univ ![a, b, c, d] ![a, b, c, d] ?_ ?_ ?_
    . -- Simplify the sum and product
      simp [Finset.sum, Finset.prod] at h₀
      ring_nf at h₀ ⊢
      exact h₀
    -- Check the constraints
    . intro i
      fin_cases i
      all_goals
        simp
        positivity
    . simp [Finset.sum]
      linear_combination h
    . intro i
      fin_cases i
      all_goals
        simp
        positivity
  calc
    _ = (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) := by ring
    -- Use the estimate above
    _ ≤ (a + 2 * b + 3 * c + 4 * d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := mul_le_mul_of_nonneg_left h₀ (by linarith)
    -- Note that a + 2b + 3c + 4d ≤ any of the sums:
    -- a + 3b + 3c + 3d; 3a + b + 3c + 3d; 3a + 3b + c + 3d; 3a + 3b + 3c + d
    -- Apply the bounds
    _ ≤ a ^ 2 * (a + 3 * b + 3 * c + 3 * d) + b ^ 2 * (3 * a + b + 3 * c + 3 * d) + c ^ 2 * (3 * a + 3 * b + c + 3 * d) + d ^ 2 * (3 * a + 3 * b + 3 * c + d) := by
      have ha : a + 3 * b + 3 * c + 3 * d ≥ a + 2 * b + 3 * c + 4 * d := by linarith
      have hb : 3 * a + b + 3 * c + 3 * d ≥ a + 2 * b + 3 * c + 4 * d := by linarith
      have hc : 3 * a + 3 * b + c + 3 * d ≥ a + 2 * b + 3 * c + 4 * d := by linarith
      have hd : 3 * a + 3 * b + 3 * c + d ≥ a + 2 * b + 3 * c + 4 * d := by linarith
      nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]
    -- Now the sum is a part of the full expansion of (a + b + c + d) ^ 3, so it is less than (a + b + c + d) ^ 3
    _ < (a + b + c + d) ^ 3 := by
      rw [← sub_pos]
      ring_nf
      positivity
    -- Use a + b + c + d = 1
    _ = 1 := by simp [h]
