import Mathlib

theorem algebra_224764 (f : ℝ → ℝ) (hf : f = fun x => 2*x^4-3*x^3+7*x^2-9*x+3) :
    ∑ᶠ x ∈ {x | f x = 0}, x^2 = 5/4 := by
  have h1 : {x : ℝ | f x = 0} = {1, 1 / 2} := by
    ext x
    simp [hf]
    constructor
    · -- Suppose $2x^{4}-3x^{3}+7x^{2}-9x+3=0$, then $x=1$ or $1/2$
      intro hx
      have h_eq : 2 * x^4 - 3 * x^3 + 7 * x^2 - 9 * x + 3 = 0 := by
        simpa using hx
      have hfactored : (x - 1) * (x - 1 / 2) * (2 * x ^ 2 + 6) = 0 := by
        nlinarith [sq_nonneg (x^2 - 3/2 * x + 1/2), sq_nonneg (x), sq_nonneg (x - 1), sq_nonneg (x - 1/2), sq_nonneg (x^2 + 3)]
      cases' (mul_eq_zero.mp hfactored) with h4 h5
      · cases' (mul_eq_zero.mp h4) with h6 h7
        · -- $x-1=0$, i.e., $x=1$
          have hx1 : x = 1 := by linarith
          left
          exact hx1
        · -- $x-1/2=0$, i.e., $x=1/2$
          have hx2 : x = (1 / 2 : ℝ) := by linarith
          have hx2' : x = (1 / 2 : ℝ) := hx2
          rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] at hx2'
          right
          exact_mod_cast hx2'
      · -- $2x^2+6=0$, no real solutions
        have : 2 * x^2 + 6 > 0 := by nlinarith [sq_nonneg (x)]
        nlinarith
    · -- If $x=1$ or $1/2$, then $2x^{4}-3x^{3}+7x^{2}-9x+3=0$.
      rintro (rfl | rfl)
      · -- $x=1$
        norm_num
      · -- $x=1/2$
        norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num