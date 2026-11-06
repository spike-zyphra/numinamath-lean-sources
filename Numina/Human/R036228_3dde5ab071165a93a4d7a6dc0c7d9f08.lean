import Mathlib

open Real Set
open scoped BigOperators

/-
A tennis ball dipped in red paint rolls around on the coordinate plane, so that it is at
\[(x,y) = (3t^2 - 9t - 5, t^2 - 3t + 2)\]at time $t,$ where $0 \le t \le 4.$  Find the length of the paint trail left by the tennis ball.
-/
theorem calculus_22127 (fx fy : ℝ → ℝ)
  (hfx : fx = λ t => 3 * t ^ 2 - 9 * t - 5) (hfy: fy = λ t => t ^ 2 - 3 * t + 2) :
  ∫ t in (0)..4, Real.sqrt ((deriv fx t) ^ 2 + (deriv fy t) ^ 2) = 17 * sqrt 10 / 2 := by
  -- We will first compute the derivatives of fx and fy
  have h1 : deriv fx = λ t => 6 * t - 9 := by
    funext x
    rw [hfx]
    rw [deriv_sub_const, deriv_sub, deriv_const_mul, deriv_const_mul, deriv_pow]
    simp
    ring_nf
    simp
    simp
    simp
    have h1: (HMul.hMul (9:ℝ)) = fun x => x * 9 := by funext x; ring
    rw [h1]
    simp
  have h2 : deriv fy = λ t => 2 * t - 3 := by
    funext x
    rw [hfy]
    rw [deriv_add_const, deriv_sub, deriv_const_mul, deriv_pow]
    simp
    simp
    simp
    have h1: (HMul.hMul (3:ℝ)) = fun x => x * 3 := by funext x; ring
    rw [h1]
    simp
  rw [h1, h2]
  simp
  ring_nf
  -- the sum of derivatives is a square root
  have h3 : (fun t:ℝ ↦ √(90 - t * 120 + t ^ 2 * 40)) = fun t:ℝ ↦ √40 * abs (t - 3 / 2) := by
    funext x
    rw [<-Real.sqrt_sq_eq_abs,<- Real.sqrt_mul]
    have h: 90 - x * 120 + x ^ 2 * 40 = (40 * (x - 3 / 2) ^ 2) := by ring
    rw [h]
    norm_num
  rw [h3]
  simp
  ring_nf
  -- split the integral into two parts
  have intervalIntegrable_abs {a b : ℝ} {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsLocallyFiniteMeasure μ] : IntervalIntegrable abs μ a b :=
    IntervalIntegrable.abs (ContinuousOn.intervalIntegrable continuousOn_id)
  have h4: (∫ (x : ℝ) in (-3 / 2)..(5 / 2), |x|) = (∫ (t : ℝ) in (-3 / 2)..0, |t|) + (∫ (t : ℝ) in (0)..(5 / 2), |t|) :=
    eq_comm.1 (intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_abs)
    (intervalIntegrable_abs))
  rw [h4]
  -- compute the pos part of integrals
  let x_sq := λ t:ℝ  => (t ^ 2) / 2
  have pos_hderiv : ∀ x ∈ Set.Ioo 0 (5 / 2), HasDerivWithinAt x_sq (abs x) (Set.Ioi x) x := by
    intros x hx
    simp at hx
    rw [abs_of_nonneg (by linarith)]
    simp only [x_sq]
    have h := HasDerivWithinAt.div_const (hasDerivWithinAt_pow 2 x (Set.Ioi x)) (2:ℝ)
    simp at h
    simp
    exact h

  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real
    (by linarith)
    (ContinuousOn.div_const (ContinuousOn.pow continuousOn_id 2) 2)
    pos_hderiv
    (integrableOn_Icc_iff_integrableOn_Ioc.2 intervalIntegrable_abs.1)]

  -- compute the neg part of integrals
  let neg_x_sq := λ t:ℝ  => -(t ^ 2) / 2
  have neg_hderiv : ∀ x ∈ Set.Ioo (-3/2) 0, HasDerivWithinAt neg_x_sq (abs x) (Set.Ioi x) x := by
    intros x hx
    simp at hx
    rw [abs_of_nonpos (by linarith)]
    simp only [neg_x_sq]
    have h := HasDerivWithinAt.div_const (HasDerivWithinAt.neg (hasDerivWithinAt_pow 2 x (Set.Ioi x))) (2:ℝ)
    simp at h
    simp
    have h_simp : (-(2 * x) / 2) = -x := by ring_nf
    rw [h_simp] at h
    exact h
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le_real
    (by linarith)
    (ContinuousOn.div_const (ContinuousOn.neg (ContinuousOn.pow continuousOn_id 2)) 2)
    neg_hderiv
    (integrableOn_Icc_iff_integrableOn_Ioc.2 intervalIntegrable_abs.1)]
  -- simplify the result
  simp
  ring_nf
  calc √40 * (17 / 4) = √(4*10) * (17 / 4) := by norm_num
    _ = √4*√10 * (17 / 4) := by rw [sqrt_mul]; norm_num
    _ = 2 * √10 * (17 / 4) := by norm_num; rw [Real.sqrt_eq_iff_eq_sq]; norm_num; norm_num; norm_num
    _ = √10 * (17 / 2) := by ring_nf
