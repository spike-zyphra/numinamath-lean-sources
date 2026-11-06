import Mathlib

/- [ Algebraic inequalities (miscellaneous) $]$

Prove that $\frac{x^{6}}{y^{2}}+\frac{y^{6}}{x^{2}} \geq x^{4}+y^{4} \quad$ for any $x$ and $y$.

# -/
theorem inequalities_173292 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    x ^ 6 / y ^ 2 + y ^ 6 / x ^ 2 ≥ x ^ 4 + y ^ 4 := by
  -- we have 0 < y ^ 2 * x ^ 2 (because x ≠ 0 and y ≠ 0)
  have h : 0 < y ^ 2 * x ^ 2 := by
    apply mul_pos
    apply pow_two_pos_of_ne_zero hy
    apply pow_two_pos_of_ne_zero hx
  field_simp
  rw [le_div_iff₀ h, ←sub_nonneg]
  ring_nf
  -- simplify the expression and get
  -- 0 ≤ -(x ^ 2 * y ^ 6) - x ^ 6 * y ^ 2 + x ^ 8 + y ^ 8
  --   = (x ^ 2 - y ^ 2) * (x ^ 6 - y ^ 6)
  suffices 0 ≤ (x ^ 2 - y ^ 2) * (x ^ 6 - y ^ 6) by
    ring_nf at this
    exact this
  -- show that 0 ≤ x ^ 2 - y ^ 2 ↔ 0 ≤ x ^ 6 - y ^ 6
  rw [mul_nonneg_iff]
  have h6 {x y : ℝ} (hxy : x ^ 2 ≤ y ^ 2) : x ^ 6  ≤ y ^ 6 := by
    rw [show 6 = 2 * 3 by norm_num, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) hxy 3
  -- consider two cases
  by_cases h : x ^ 2 ≤ y ^ 2
  -- if x ^ 2 ≤ y ^ 2 then x ^ 6 ≤ y ^ 6 and the product
  -- (x ^ 2 - y ^ 2) * (x ^ 6 - y ^ 6) is nonnegative
  · right
    exact ⟨by linarith, by linarith [h6 h]⟩
  -- if y ^ 2 < x ^ 2 then y ^ 6 ≤ x ^ 6 and the product
  -- (x ^ 2 - y ^ 2) * (x ^ 6 - y ^ 6) is nonnegative
  · left
    refine ⟨by linarith, ?_⟩
    push_neg at h
    linarith [h6 (le_of_lt h)]