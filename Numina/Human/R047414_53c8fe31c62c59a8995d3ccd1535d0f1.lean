import Mathlib

-- Let $f$ be a function from the nonnegative integers to the positive reals such that $f(x+y)=f(x) \cdot f(y)$ holds for all nonnegative integers $x$ and $y$. If $f(19)=524288 k$, find $f(4)$ in terms of $k$.
open Real

theorem Algebra_609307 {f : ℕ → ℝ}  {k : ℝ} (hpos : ∀ (x : ℕ), f x > 0)
  (hf : ∀ x y : ℕ, f (x + y) = f x * f y) 
  (h19 : f 19 = 524288 * k) : 
  f 4 = 16 * k ^ (4 / (19 : ℝ)) := by
  -- use `f (0 + 0) = f(0) * f(0)` and `f 0 > 0` to prove `f (0) = 1`
  have f_zero : f 0 = 1 := by 
    obtain hf₀ := hf 0 0
    simp at hf₀
    obtain f_zero_pos := hpos 0
    have f_zero_neq : f 0 ≠ 0 := Ne.symm (ne_of_lt (hpos 0))
    exact (mul_eq_left₀ f_zero_neq).mp (Eq.symm hf₀)
-- use induction to prove `f (m * n) = f(m) ^ n`
  have eq_aux (m n : ℕ): f (m * n) = f (m) ^ n := by 
    induction n with 
    | zero => 
      simp
      exact f_zero
    | succ t ih =>
      ring_nf
      obtain hf' := hf m (m * t)
      rw [hf', ih]
  have f_eq : (f 4) ^ (19 : ℝ) = (f 19) ^ (4 : ℝ) := by 
    calc 
      _ = f (4 * 19) := by 
        norm_cast
        exact Eq.symm (eq_aux 4 19)
      _ = (f 19) ^ 4 := by 
        rw [mul_comm]
        exact eq_aux 19 4
    norm_cast
  have f_eq' : (f 4) = (f 19) ^ (4 / (19 : ℝ)):= by 
    have eq_aux' : 4 / (19 : ℝ) = 4 * (19⁻¹) := by norm_num
    rw [eq_aux', rpow_mul, ←f_eq]
    have f_four : f 4 ≥ 0 := by 
      obtain pos := hpos 4
      linarith
    have neq19 : (19 : ℝ) ≠ 0:= by norm_num
    refine Eq.symm (Real.rpow_rpow_inv f_four neq19)
    obtain pos' := hpos 19
    linarith
  rw [f_eq', h19]
  rw [mul_rpow]
  congr
  have two_pow : (2 : ℝ) ^ (19 : ℝ) = 524288 := by norm_num
  rw [←two_pow]
  rw [←rpow_mul]
  norm_num
  positivity
  positivity
  obtain h19_pos := hpos 19
  rw [h19] at h19_pos
  linarith
  