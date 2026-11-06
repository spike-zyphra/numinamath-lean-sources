import Mathlib

import Mathlib

open Real Set
open scoped Real

/--  If the acute angle $\theta$ satisfies
$$
  \sin(\pi \cos \theta) = \cos(\pi \sin \theta)
$$,
Then, what is $\sin 2\theta$ ?-/
theorem Trigonometry_4174 (θ : Real) (hθ : θ ∈ Ioo 0 (π / 2)) (h : sin (π * cos θ) = cos (π * sin θ)) : sin (2 * θ) = 3 / 4 := by
  have image_sin : sin '' Ioo 0 (π / 2) ⊆ _ := (Real.strictMonoOn_sin.mono (Set.Icc_subset_Icc (by simp; positivity) (by rfl))).image_Ioo_subset
  have image_cos : cos '' Ioo 0 (π / 2) ⊆ _ := (Real.strictAntiOn_cos.mono (Set.Icc_subset_Icc (by rfl) (by simp; positivity))).image_Ioo_subset
  simp at image_sin image_cos
  have hsin := image_sin hθ
  have hcos := image_cos hθ
  simp at hsin hcos
  have hsincos : 0 < sin (π * cos θ) := by
    apply sin_pos_of_mem_Ioo
    simp [mem_Ioo, mul_pos_iff_of_pos_right, *, pi_pos]
  rw [h] at hsincos
  -- Transformation Using Sine and Cosine Identities,
  -- we get $\pi \sin \theta \in \left[0, \frac 1 2 \right]$
  replace hsin : 0 < sin θ ∧ sin θ < 1 / 2 := by
    have : π * sin θ < π * 2⁻¹ := by
      rw [← div_eq_mul_inv]
      contrapose! hsincos
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      linarith
      convert_to _ ≤ π * (1 + 1 / 2)
      · rw [mul_add]; field_simp
      · rw [mul_le_mul_left pi_pos]; linarith
    rw [mul_lt_mul_left pi_pos] at this
    aesop
  have : 3 / 4 < cos θ ^ 2 := by
    have := Real.cos_sq_add_sin_sq θ
    nlinarith
  have : 1 / 2 < cos θ := by
    nlinarith
  have := Real.cos_sub_pi_div_two (π * cos θ)
  rw [h, cos_eq_cos_iff] at this
  obtain ⟨k, H⟩ := this
  -- Transformation Using Sine and Cosine Identities,
  -- we get $\pi \cos \theta \in \left[\frac{\pi}{2}, \pi \right]$
  have hpicos : π / 2 < π * cos θ ∧ π * cos θ < π := by
    constructor
    · rw [div_eq_mul_inv, mul_lt_mul_left]
      field_simp [this]
      exact pi_pos
    · exact mul_lt_of_lt_one_right pi_pos hcos.2
  have hpisin : 0 < π * sin θ ∧ π * sin θ < π / 2 := by
    constructor <;> nlinarith
  obtain ⟨rfl⟩ : k = 0 := by
    by_contra hk
    replace hk : (k : ℝ) <= -1 ∨ 1 <= (k : ℝ) := by norm_cast; change k ≤ -1 ∨ _; omega
    cases H <;> cases hk <;> nlinarith
  -- From $\cos A = \cos B$, we note : $\pi \sin \theta = \pi \cos \theta - \frac{\pi}{2}$. Simplifying, we get $\sin \theta = \cos \theta - \frac{1}{2}$.
  replace H : sin θ = cos θ - 1 / 2 := by
    rw [← mul_right_inj' (pi_pos.ne' : π ≠ 0)]
    simp at H
    cases H <;> linarith
  rw [sin_two_mul, H]
  rw [← pow_left_inj (by linarith) (by linarith) (two_ne_zero : 2 ≠ 0), sin_eq_sqrt_one_sub_cos_sq hθ.1.le (by linarith [hθ.2]), sq_sqrt (by simp [abs_cos_le_one])] at H
  replace H : 2 * cos θ * cos θ + (-1 * cos θ) + (-3 / 4) = 0 := by
    rw [sub_eq_iff_eq_add] at H
    ring_nf at H
    rw [← sub_eq_iff_eq_add'] at H
    ring_nf
    rw [← H]
    ring
  -- Solving the Quadratic Equation: we get $\cos \theta = \frac {1 + \sqrt 7} {4}$
  have discr : discrim (R := ℝ) 2 (-1) (-3 / 4) = √7 * √7 := by
    unfold discrim
    rw [mul_self_sqrt (by norm_num)]
    ring
  rw [mul_assoc, quadratic_eq_zero_iff (by norm_num) discr] at H
  norm_num at H
  replace H : cos θ = (1 + √7) / 4 := by
    refine H.resolve_right (fun H ↦ ?_)
    rw [H] at hcos
    simp [Real.sqrt_lt] at hcos
  rw [H]
  ring_nf
  norm_num
