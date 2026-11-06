import Mathlib

/- Soit $x, y$ et $z$ des réels strictement positifs tels que $x y+y z+z x=3$.
Démontrer que

$$
\frac{x+3}{y+z}+\frac{y+3}{z+x}+\frac{z+3}{x+y}+3 \geqslant 27 \frac{(\sqrt{x}+\sqrt{y}+\sqrt{z})^{2}}{(x+y+z)^{3}}
$$ -/
theorem inequalities_605810 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y + y * z + z * x = 3) :
    (x + 3) / (y + z) + (y + 3) / (z + x) + (z + 3) / (x + y) + 3 ≥ 27 * ((Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2 / (x + y + z) ^ 3) := by
  -- Prove the Cauchy-Schwarz inequality.
  have CS_ineq (x₁ y₁ z₁ x₂ y₂ z₂ : ℝ) : (x₁ * x₂ + y₁ * y₂ + z₁ * z₂) ^ 2 ≤ (x₁ ^ 2 + y₁ ^ 2 + z₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2 + z₂ ^ 2) := by
    nlinarith [sq_nonneg (x₁ * y₂ - y₁ * x₂), sq_nonneg (y₁ * z₂ - z₁ * y₂), sq_nonneg (z₁ * x₂ - x₁ * z₂)]
  -- Let s = x + y + z.
  let s := x + y + z
  -- Show that the left-hand-side of the inequality is greater than or equal to 9(s + 3)/(2s).
  have h₀ : (x + 3) / (y + z) + (y + 3) / (z + x) + (z + 3) / (x + y) + 3 ≥ 9 * (s + 3) / (2 * s) := by
    calc
      (x + 3) / (y + z) + (y + 3) / (z + x) + (z + 3) / (x + y) + 3
      _ = ((x + 3) / (y + z) + 1) + ((y + 3) / (z + x) + 1) + ((z + 3) / (x + y) + 1) := by ring
      _ = (s + 3) * (1 / (y + z) + 1 / (z + x) + 1 / (x + y)) := by
        -- Reduce each group of terms to a common denominator.
        iterate 3 rw [div_add_one (by linarith)]
        iterate 2 rw [mul_add]
        iterate 3 rw [mul_one_div]
        congrm ?_ / ?_ + ?_ / ?_ + ?_ / ?_
        all_goals
          ring
      _ ≥ 9 * (s + 3) / (2 * s) := by
        -- It suffices to show that 9 ≤ (1 / (y + z) + 1 / (z + x) + 1 / (x + y)) * (2 * s).
        nth_rewrite 2 [mul_comm]
        rw [mul_div_assoc, ge_iff_le, mul_le_mul_left (by positivity), div_le_iff₀ (by positivity)]
        -- Simplify the expression after applying the Cauchy-Schwarz inequality.
        specialize CS_ineq (1 / Real.sqrt (y + z)) (1 / Real.sqrt (z + x)) (1 / Real.sqrt (x + y)) (Real.sqrt (y + z)) (Real.sqrt (z + x)) (Real.sqrt (x + y))
        iterate 3 rw [div_mul_cancel₀ _ (by positivity), div_pow, Real.sq_sqrt (by positivity)] at CS_ineq
        norm_num [-one_div] at CS_ineq
        rw [show 2 * s = y + z + (z + x) + (x + y) by ring]
        exact CS_ineq
    -- Prove the Arithmetic-Quadratic Mean inequality.
  have AM_QM_ineq (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : ((x + y + z) / 3) ^ 2 ≤ (x ^ 2 + y ^ 2 + z ^ 2) / 3 := by
    -- This is equivalent to (x - y)² + (y - z)² + (z - x)² ≥ 0.
    linarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  -- Show that ((√x + √y + √z) / 3)² ≤ s / 3.
  have h₁ : ((Real.sqrt x + Real.sqrt y + Real.sqrt z) / 3) ^ 2 ≤ s / 3 := by
    specialize AM_QM_ineq (Real.sqrt x) (Real.sqrt y) (Real.sqrt z) (by apply Real.sqrt_nonneg) (by apply Real.sqrt_nonneg) (by apply Real.sqrt_nonneg)
    iterate 3 rw [Real.sq_sqrt (by positivity)] at AM_QM_ineq
    exact AM_QM_ineq
  -- Show that s² ≥ 3².
  have h₂ : s ^ 2 ≥ 3 ^ 2 := by
    calc
      s ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
        ring_nf
      _ ≥ (x * y + y * z + z * x) + 2 * (x * y + y * z + z * x) := by
        apply add_le_add
        linarith only [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
        rfl
      _ = 3 ^ 2 := by
        -- Use the fact that xy + yz + zx = 3 stated in the hypothesis.
        linarith only [h]
  -- Show that s ≥ 3.
  rw [ge_iff_le, sq_le_sq₀ (by norm_num) (by positivity)] at h₂
  -- Summarize the known inequalities above to arrive at the desired result.
  calc
    (x + 3) / (y + z) + (y + 3) / (z + x) + (z + 3) / (x + y) + 3 ≥ 9 * (s + 3) / (2 * s) := h₀
    _ ≥ 81 / s ^ 2 := by
      rw [ge_iff_le, div_le_div_iff₀ (by positivity) (by positivity)]
      -- Use the fact that 3 ≤ s and 0 < s to solve the inequality.
      nlinarith only [show 0 < s by positivity, h₂]
    _ ≥ 27 * ((√x + √y + √z) ^ 2 / (x + y + z) ^ 3) := by
      -- Use h₁ to achieve the desired result.
      rw [show x + y + z = s by simp [s], ge_iff_le, <-mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity), show s ^ 3 = s * s ^ 2 by ring]
      rw [<-mul_assoc, mul_le_mul_right (by positivity)]
      rw [div_pow, div_le_div_iff₀ (by norm_num) (by norm_num)] at h₁
      linarith only [h₁]
  
