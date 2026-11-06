import Mathlib

/- 9.072. Find solution for x: $x^{8}-6 x^{7}+9 x^{6}-x^{2}+6 x-9<0$.
. -/
theorem inequalities_190146 (f : ℝ → ℝ) (hf : f = λ x => x^8 - 6 * x^7 + 9 * x^6 - x^2 + 6 * x - 9) :
    ∀ x, f x < 0 ↔ x ∈ Set.Ioo (-1) 1 := by
  -- factorize the expression as (x-3)^2 * (x^6-1)
  have (x: ℝ) : f x = (x - 3)^2 * (x^6 - 1) := by
    rw [hf]
    simp
    ring
  simp_rw [this]

  -- if x-3 = 0, inequality is false, and otherwise (x-3)^2 > 0 so inequality is equivalent to x^6-1 < 0
  have (x : ℝ) : (x - 3)^2 * (x^6 - 1) < 0 ↔ x^6 - 1 < 0 := by
    obtain h | h := @or_not (x-3 = 0)
    . have : x = 3 := by linarith
      rw [this]
      simp; norm_num
    . calc
        (x - 3) ^ 2 * (x ^ 6 - 1) < 0 ↔ (x - 3) ^ 2 * (x ^ 6 - 1) < (x-3)^2 * 0 := by ring_nf
        _ ↔ x ^ 6 - 1 < 0 := by
          refine mul_lt_mul_left ?_
          positivity
  simp_rw [this]

  -- x^6 - 1 < 0 is equivalent to |x| < 1
  have (x : ℝ) : x^6 - 1 < 0 ↔ |x| < 1 := by calc
    x^6 - 1 < 0 ↔ x^6 < 1 := by constructor <;> (rintro _; linarith)
    _ ↔ |x|^6 < 1 := by
      have : x^6 = |x|^6 := by
        refine Eq.symm (Even.pow_abs ?_ x)
        use 3
      rw [this]
    _ ↔ |x|^6 < 1^6 := by simp
    _ ↔ |x| < 1 := by
      refine pow_lt_pow_iff_left₀ ?_ ?_ ?_ <;> simp
  simp_rw [this]
  -- |x|-1 < 0 is equivalent to x ∈ (-1, 1)
  simp_rw [abs_lt]
  simp