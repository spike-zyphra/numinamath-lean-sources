import Mathlib

open Real Set

theorem inequalities_598124 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z = 1) :
    (28 / 3) ^ 3 ≤ (1 / x^2 + x) * (1 / y^2 + y) * (1 / z^2 + z) := by
  let f (x : ℝ) : ℝ := log (1 / x^2 + x)
  have hf : ConvexOn ℝ (Ioo 0 1) f := by
    have hfderiv (x : ℝ) (hx : 0 < x) : deriv f x = (x ^ 3 - 2) / (x ^ 4 + x) := by
      rw [deriv.log, deriv_add, deriv_div]
      simp [-one_div]
      field_simp
      ring
      . simp
      . simp
      . positivity
      . exact DifferentiableAt.div (by simp) (by simp) (by positivity)
      . simp
      . simp [-one_div]
        exact DifferentiableAt.div (by simp) (by simp) (by positivity)
      . positivity
    have hfderiv2 (x : ℝ) (hx : 0 < x) : deriv^[2] f x = (-x ^ 6 + 10 * x ^ 3 + 2) / (x ^ 4 + x) ^ 2 := by
      simp
      rw [← derivWithin_of_isOpen (s := Ioi 0) isOpen_Ioi hx]
      rw [derivWithin_congr (f₁ := deriv f) (f := fun x ↦ (x ^ 3 - 2) / (x ^ 4 + x)) (s := Ioi 0) hfderiv (hfderiv x hx)]
      rw [derivWithin_of_isOpen (s := Ioi 0) isOpen_Ioi hx]
      rw [deriv_div (by simp) (by simp) (by positivity)]
      simp
      field_simp
      ring
    apply convexOn_of_deriv2_nonneg'
    . exact convex_Ioo _ _
    . simp [f, -one_div]
      refine DifferentiableOn.log ?_ (by intro x hx; replace hx := (mem_Ioo.1 hx).1; positivity)
      refine DifferentiableOn.add ?_ differentiableOn_id
      refine DifferentiableOn.div (differentiableOn_const _) ?_ (by intro x hx; replace hx := (mem_Ioo.1 hx).1; positivity)
      exact DifferentiableOn.pow differentiableOn_id _
    . refine DifferentiableOn.mono (t := Ioi 0) ?_ Ioo_subset_Ioi_self
      rw [differentiableOn_congr (f₁ := deriv f) (f := fun x ↦ (x ^ 3 - 2) / (x ^ 4 + x)) (s := Ioi 0) hfderiv]
      exact DifferentiableOn.div (Differentiable.differentiableOn (by simp)) (Differentiable.differentiableOn (by simp)) (by intro x hx; simp at hx; positivity)
    . intro x hx
      obtain ⟨hx₁, hx₂⟩ := hx
      rw [hfderiv2 x hx₁]
      have H : 0 < -x ^ 6 + 10 * x ^ 3 + 2 := by
        replace hx₂ : 1 - x > 0 := by linarith only [hx₂]
        rw [show -x ^ 6 + 10 * x ^ 3 + 2 = 9 * x ^ 3 + 2 + x ^ 3 * (1 - x) * (x ^ 2 + x + 1) by ring]
        exact add_pos (by positivity) (by positivity)
      positivity
  have H := ConvexOn.map_sum_le (w := ![1/3, 1/3, 1/3]) (p := ![x, y, z]) (hf := hf) (t := Finset.univ) ?_ ?_ ?_
  rotate_left
  {
    intro i
    fin_cases i <;> simp
  }
  {
    simp [Finset.sum]
    norm_num
  }
  {
    intro i
    fin_cases i
    all_goals
      simp
      constructor
      . assumption
      . linarith
  }
  simp [Finset.sum] at H
  rw [show 3⁻¹ * x + (3⁻¹ * y + 3⁻¹ * z) = 1 / 3 by linarith only [h]] at H
  replace H : 3 * f (1 / 3) ≤ f x + f y + f z := by linarith only [H]
  simp only [f] at H
  rw [← log_mul (by positivity) (by positivity),
      ← log_mul (by positivity) (by positivity),
      ← log_rpow (by norm_num) 3,
      show ((1 / (1 / 3) ^ 2 + 1 / 3) : ℝ) ^ (3 : ℝ) = (28 / 3) ^ 3 by norm_num] at H
  rwa [StrictMonoOn.le_iff_le strictMonoOn_log (by simp) (by simp; positivity)] at H
