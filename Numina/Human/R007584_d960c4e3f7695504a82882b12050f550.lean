import Mathlib

open Real Polynomial intervalIntegral

open scoped Interval

/- Find all $y>1$ satisfying $\int_{1}^{y} x \ln x d x=\frac{1}{4}$. -/
theorem calculus_608264 (y : ℝ) (hy : y > 1) :
    ∫ (x : ℝ) in (1 : ℝ)..y, x * log x = 1 / 4 ↔ y = √ (exp 1) := by
  let u := log
  let v : ℝ → ℝ := fun x ↦ 1 / 2 * (x ^ 2)
  let u' : ℝ → ℝ := fun x ↦ 1 / x
  let v' : ℝ → ℝ := fun x ↦ x
  have ucts : ContinuousOn u [[1, y]] := by
    apply ContinuousOn.log
    · exact continuousOn_id' [[1, y]]
    · intro x hx
      rw [Set.uIcc_of_le, Set.mem_Icc] at hx
      linarith only [hx]
      exact hy.le
  have vd : Differentiable ℝ v := by simp [v]
  have vcts : ContinuousOn v [[1, y]] := Continuous.continuousOn (Differentiable.continuous vd)
  have hys : [[1, y]] = Set.Icc 1 y := Set.uIcc_of_lt hy
  have huu' : ∀ x ∈ [[1, y]], HasDerivAt u (u' x) x := by
    intro x hx
    rw [hys] at hx
    simp only [Set.mem_Icc] at hx
    simp [u, u']
    exact hasDerivAt_log (by linarith only [hx])
  have hvv' : ∀ x ∈ [[1, y]], HasDerivAt v (v' x) x := by
    intro x hx
    rw [hys] at hx
    simp only [Set.mem_Icc] at hx
    have dv : deriv v = v' := by simp [v, v']
    rw [← dv]
    simp only [hasDerivAt_deriv_iff]
    exact vd x
  have hu' : IntervalIntegrable u' MeasureTheory.volume 1 y := by
    simp only [one_div, intervalIntegrable_inv_iff, u'] ; right
    simp only [hys, Set.mem_Icc, not_and, not_le, isEmpty_Prop, zero_lt_one, IsEmpty.forall_iff]
  have hv' : IntervalIntegrable v' MeasureTheory.volume 1 y :=
    intervalIntegral.intervalIntegrable_id
  have int1 : ∫ (x : ℝ) in (1 : ℝ)..y, u' x * v x = 1 / 4 * y ^ 2 - 1 / 4 := by
    calc
      _ = ∫ (x : ℝ) in (1 : ℝ)..y, 1 / 2 * x := by
        apply integral_congr
        intro x hx
        rw [hys] at hx
        simp only [Set.mem_Icc] at hx
        simp only [u', v]
        have : x ≠ 0 := by
          linarith only [hx]
        field_simp [this] ; ring
      _ = 1 / 2 * ∫ (x : ℝ) in (1 : ℝ)..y, x := by apply integral_const_mul
      _ = _ := by
        simp only [one_div, integral_id, one_pow]
        field_simp ; left
        norm_num
  have int2 : ∫ (x : ℝ) in (1 : ℝ)..y, x * log x = 1 / 2 * y ^ 2 * log y - 1 / 4 * y ^ 2 + 1 / 4 :=
      calc
        _ = ∫ (x : ℝ) in (1 : ℝ)..y, u x * v' x := by
          congr 1 ; simp only [mul_comm, u, v']
        _ = u y * v y - u 1 * v 1 - ∫ (x : ℝ) in (1 : ℝ)..y, u' x * v x :=
          intervalIntegral.integral_mul_deriv_eq_deriv_mul huu' hvv' hu' hv' 
        -- Applying integration by parts with $u=\ln x$ and $v=\frac{1}{2} x^{2}$,
        -- we get $$ \int_{1}^{y} x \ln x d x=\left.\frac{1}{2} x^{2} \ln x\right|_{1} ^{y}-\frac{1}{2} \int_{1}^{y} x d x
        _ = 1 / 2 * y ^ 2 * log y - 1 / 4 * y ^ 2 + 1 / 4 := by
          rw [int1]
          simp only [log_one, one_pow, mul_one, zero_mul, sub_zero, u, v]
          ring
        -- =\frac{1}{2} y^{2} \ln y-\frac{1}{4} y^{2}+\frac{1}{4} $$
  rw [int2]
  clear* -y hy
  field_simp
  rw [mul_eq_zero]
  norm_num
  rw [sub_eq_zero, mul_assoc]
  nth_rw 3 [mul_comm]
  rw [mul_eq_mul_left_iff]
  have : y ^ 2 ≠ 0 := by
    apply ne_of_gt
    apply pow_pos
    linarith only [hy]
  simp only [this, or_false]
  rw [← eq_div_iff (by norm_num)]
  norm_num
  -- So $y^{2} \ln y=\frac{1}{2} y^{2}$.
  have hlog : log (√(rexp 1)) = 1 / 2 := by
    rw [log_sqrt (by exact exp_nonneg 1)]
    field_simp
  rw [← hlog]
  constructor
  · apply Real.log_injOn_pos 
    -- Since $y&gt;1$, we obtain $\ln y=\frac{1}{2}$, and thus $y=\sqrt{e}$.-/
    · simp only [Set.mem_Ioi]
      linarith only [hy] 
    · simp only [Set.mem_Ioi]
      rw [sqrt_pos] 
      exact exp_pos 1 
  · intro h 
    congr 







