import Mathlib

open Real Set
open scoped BigOperators

/-The maximum and minimum values of the function $f(x) = (x-2)e^x$ in the interval $[0, 2]$ are respectively.$-/
theorem algebra_9146 {f : ℝ → ℝ} (hf : f = λ x => (x - 2) * exp x)
(I : Set ℝ) (hI : I = Icc 0 2) :
IsGreatest (image f I) 0 ∧ IsLeast (image f I) (-exp 1) := by
  subst hI
  -- Step 1: Split f into product of two functions
  let u : ℝ → ℝ := fun x => x - 2
  let v : ℝ → ℝ := fun x => Real.exp x
  -- Step 2: Prove differentiability of both parts
  have hu : Differentiable ℝ u := by
    intro x
    simp only [u, differentiableAt_id', differentiableAt_const, DifferentiableAt.sub]
  have hv : Differentiable ℝ v := by
    intro x
    simp only [v, Real.differentiableAt_exp]
  -- Step 3: Prove f is differentiable using product rule
  have hfd : Differentiable ℝ f := by
    simp [hf]
  -- Step 4: Calculate f'(x) = (x-1)eˣ
  have df : deriv f = fun x => (x - 1) * Real.exp x := by
    ext x
    have := deriv_mul (𝕜 := ℝ) (𝔸 := ℝ) (hu x) (hv x)
    simp_all [u, v, this]
    ring
  -- Step 5: Establish continuity from differentiability
  have hfc : Continuous f := Differentiable.continuous hfd
  -- Step 6: Prove monotonicity on [0,1] and [1,2]
  -- Decreasing on [0,1] since f'(x) ≤ 0
  have fant : AntitoneOn f (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (Continuous.continuousOn hfc) (Differentiable.differentiableOn hfd)
    intro x hx
    simp_rw [df]
    rw [interior_Icc, mem_Ioo] at hx
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (exp_nonneg x)
  -- Increasing on [1,2] since f'(x) ≥ 0
  have fmot : MonotoneOn f (Icc 1 2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 1 2)
      (Continuous.continuousOn hfc) (Differentiable.differentiableOn hfd)
    intro x hx
    simp_rw [df]
    rw [interior_Icc, mem_Ioo] at hx
    exact mul_nonneg (by linarith) (exp_nonneg x)
  clear hfc hfd df hu hv u v
  constructor
  -- Step 7: Prove maximum value is 0
  · have fmax1 : IsGreatest (image f (Icc (0 : ℝ) 1)) (f 0) :=
      AntitoneOn.map_isLeast fant (isLeast_Icc (by norm_num))
    have fmax2 : IsGreatest (image f (Icc (1 : ℝ) 2)) (f 2) :=
      MonotoneOn.map_isGreatest fmot (isGreatest_Icc (by norm_num))
    have := IsGreatest.union fmax1 fmax2
    have imf : image f (Icc 0 2) = image f (Icc 0 1) ∪ image f (Icc 1 2) := by
      have Iu : (Icc (0 : ℝ) 1) ∪ (Icc 1 2) = (Icc 0 2) :=
        Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
      have imu := Set.image_union f (Icc 0 1) (Icc 1 2)
      rw [Iu] at imu
      exact imu
    have fleq : max (f 0) (f 2) = 0 := by simp [hf]
    rwa [← imf, fleq] at this
  -- Step 8: Prove minimum value is -e
  · have fmin1 : IsLeast (image f (Icc 0 1)) (f 1) :=
      AntitoneOn.map_isGreatest fant (isGreatest_Icc (by norm_num))
    have fmin2 : IsLeast (image f (Icc 1 2)) (f 1) :=
      MonotoneOn.map_isLeast fmot (isLeast_Icc (by norm_num))
    have := IsLeast.union fmin1 fmin2
    have imf : image f (Icc 0 2) = image f (Icc 0 1) ∪ image f (Icc 1 2) := by
      have Iu : (Icc (0 : ℝ) 1) ∪ (Icc 1 2) = (Icc 0 2) :=
        Set.Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)
      have imu := Set.image_union f (Icc 0 1) (Icc 1 2)
      rw [Iu] at imu
      exact imu
    have fleq : min (f 1) (f 1) = - exp 1 := by simp only [hf, min_self] ; norm_num
    rwa [← imf, fleq] at this
