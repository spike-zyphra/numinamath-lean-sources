import Mathlib

open Real Set
open scoped Real

/-Find the degree measure of the least positive angle $\theta$ for which
\[\tan \theta = \frac{\cos 5^\circ \cos 20^\circ + \cos 35^\circ \cos 50^\circ - \sin 5^\circ \sin 20^\circ - \sin 35^\circ \sin 50^\circ}{\sin 5^\circ \cos 20^\circ - \sin 35^\circ \cos 50^\circ + \cos 5^\circ \sin 20^\circ - \cos 35^\circ \sin 50^\circ}.\]-/
theorem calculus_18551 :
  IsLeast {θ : ℝ | 0 < θ ∧ tan θ = (cos (5 * π / 180) * cos (20 * π / 180) + cos (35 * π / 180) * cos (50 * π / 180) -
    sin (5 * π / 180) * sin (20 * π / 180) - sin (35 * π / 180) * sin (50 * π / 180)) / (sin (5 * π / 180) * cos (20 * π / 180) -
    sin (35 * π / 180) * cos (50 * π / 180) + cos (5 * π / 180) * sin (20 * π / 180) - cos (35 * π / 180) * sin (50 * π / 180))} (120 * π / 180) := by
  have tan_pi_mul_two_div_three : tan (π * (2 / 3)) = -√3 := by
      rw [←neg_eq_iff_eq_neg, ←tan_pi_sub]
      ring_nf
      rw [mul_div, mul_one, tan_pi_div_three]

  have : {θ |  0 < θ ∧  tan θ =
        (cos (5 * π / 180) * cos (20 * π / 180) + cos (35 * π / 180) * cos (50 * π / 180) -
         sin (5 * π / 180) * sin (20 * π / 180) - sin (35 * π / 180) * sin (50 * π / 180)) /
        (sin (5 * π / 180) * cos (20 * π / 180) - sin (35 * π / 180) * cos (50 * π / 180) +
         cos (5 * π / 180) * sin (20 * π / 180) - cos (35 * π / 180) * sin (50 * π / 180))} =
          {θ |  0 < θ ∧ tan θ = tan (120 * π / 180) } := by
    ext x
    simp
    intro hx
    -- commute the terms of the numerator
    have : cos (5 * π / 180) * cos (20 * π / 180) + cos (35 * π / 180) * cos (50 * π / 180) -
           sin (5 * π / 180) * sin (20 * π / 180) - sin (35 * π / 180) * sin (50 * π / 180) =
           cos (5 * π / 180) * cos (20 * π / 180) - sin (5 * π / 180) * sin (20 * π / 180) +
          (cos (35 * π / 180) * cos (50 * π / 180) - sin (35 * π / 180) * sin (50 * π / 180)) := by linarith
    rw [this, ←cos_add, ←cos_add]
    -- commute the terms of the denominator
    have : sin (5 * π / 180) * cos (20 * π / 180) - sin (35 * π / 180) * cos (50 * π / 180) +
           cos (5 * π / 180) * sin (20 * π / 180) - cos (35 * π / 180) * sin (50 * π / 180) =
           sin (5 * π / 180) * cos (20 * π / 180) + cos (5 * π / 180) * sin (20 * π / 180) -
           (sin (35 * π / 180) * cos (50 * π / 180) + cos (35 * π / 180) * sin (50 * π / 180)) := by linarith
    -- From the angle addition formula, the numerator is
    -- \begin{align*}
    -- &(\cos 5^\circ \cos 20^\circ - \sin 5^\circ \sin 20^\circ) + (\cos 35^\circ \cos 50^\circ -  \sin 35^\circ \sin 50^\circ) \\
    -- &= \cos (5^\circ + 20^\circ) + \cos (35^\circ + 50^\circ) \\
    -- &= \cos 25^\circ + \cos 85^\circ.
    -- \end{align*}From the sum-to-product formula, $\cos 25^\circ + \cos 85^\circ = 2 \cos 55^\circ \cos 30^\circ.$
    -- Similarly, the denominator is
    -- \begin{align*}
    -- &\sin 5^\circ \cos 20^\circ - \sin 35^\circ \cos 50^\circ + \cos 5^\circ \sin 20^\circ - \cos 35^\circ \sin 50^\circ) \\
    -- &= (\sin 5^\circ \cos 20^\circ +  \cos 5^\circ \sin 20^\circ) - (\sin 35^\circ \cos 50^\circ + \cos 35^\circ \sin 50^\circ) \\
    -- &= \sin (5^\circ + 20^\circ) - \sin (35^\circ + 50^\circ) \\
    -- &= \sin 25^\circ - \sin 85^\circ \\
    -- &= -2 \sin 30^\circ \cos 55^\circ,
    -- \end{align*}
    rw [this, ←sin_add, ←sin_add]
    rw [show 5 * π / 180 + 20 * π / 180 = 25 * π / 180 by linarith]
    rw [show 35 * π / 180 + 50 * π / 180 = 85 * π / 180 by linarith]
    -- so the expression is equal to
    -- \[\frac{2 \cos 55^\circ \cos 30^\circ}{-2 \sin 30^\circ \cos 55^\circ} = -\frac{\cos 30^\circ}{\sin 30^\circ} = -\sqrt{3} = \tan 120^\circ.\]Hence, the smallest such $\theta$ is $\boxed{120^\circ}.$
    have : cos (25 * π / 180) + cos (85 * π / 180) =  2 * cos (55 * π / 180) * cos (30 * π / 180) ∧
           sin (25 * π / 180) - sin (85 * π / 180) = -2 * sin (30 * π / 180) * cos (55 * π / 180) := by
      rw [sin_sub_sin, cos_add_cos]
      constructor
      · ring_nf
        have : cos (π * (-1 / 6)) = cos (π * (1 / 6)) := by 
          rw [mul_div, mul_div, mul_one, mul_neg_one, neg_div, cos_neg]
        rw [this]
      · ring_nf
        have : sin (π * (-1 / 6)) = - sin (π * (1 / 6)) := by 
          rw [mul_div, mul_div, mul_one, mul_neg_one, neg_div, sin_neg]
        rw [this]
        ring_nf
    rw [this.1, this.2]
    ring_nf
    rw [mul_comm, mul_comm (cos (π * (11 / 36))), mul_assoc]
    have : cos (π * (11 / 36)) * (cos (π * (11 / 36)))⁻¹ = 1 := by
      apply mul_inv_cancel₀
      apply cos_ne_zero_iff.mpr
      by_contra!
      obtain ⟨p, hp⟩ := this
      have : (11 / 36) = (2 * p + 1 : ℝ) / 2 := by
        have : (11 / 36) = ((2 * ↑p + 1) * π / 2) / π := by
          rw [hp.symm,  mul_comm, ←mul_div, div_self, mul_one]
          exact pi_ne_zero
        rw [this]
        ring_nf
        rw [mul_assoc, show π * π⁻¹ = 1 by apply mul_inv_cancel₀ pi_ne_zero]
        linarith
      have : 11 = 18 * (2 * p + 1 : ℝ) := by linarith
      norm_cast at this
      omega
    rw [this, mul_one, ←one_div, mul_comm, mul_div, mul_one]
    rw [tan_pi_mul_two_div_three]
    have : -(cos (π * (1 / 6)) / sin (π * (1 / 6))) = -√3 := by
      rw [mul_div, mul_one, cos_pi_div_six, sin_pi_div_six]
      linarith
    rw [this]

  rw [this]
  unfold IsLeast
  simp
  use (by linarith [pi_gt_three])
  apply mem_lowerBounds.mpr
  simp
  intro x hx₁ hx₂
  have my_lemma (x y : ℝ) (h₁: cos x ≠ 0) (h₂ : cos y ≠ 0)
    : tan x = tan y ↔ ∃(k : ℤ), x = y + k * π := by
    constructor
    · intro h
      rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, div_eq_div_iff h₁ h₂] at h
      rw [←sub_eq_zero, mul_comm (sin y), ←sin_sub, sin_eq_zero_iff] at h
      obtain ⟨k, hk⟩ := h
      use k
      linarith
    · rintro ⟨k, hk⟩
      rw [hk]
      exact tan_add_int_mul_pi _ _
  specialize my_lemma x (120 * π / 180)
  have : cos x ≠ 0 := by
    intro hx
    rw [tan_eq_sin_div_cos, hx] at hx₂
    ring_nf at hx₂
    rw [tan_pi_mul_two_div_three, ←neg_eq_iff_eq_neg, neg_zero, Eq.comm] at hx₂
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)] at hx₂
    simp at hx₂
  specialize my_lemma this
  have : cos (120 * π / 180) ≠ 0 := by
    have : cos (120 * π / 180) = -cos (π / 3) := by
      rw [←cos_pi_sub]; ring_nf
    rw [this, cos_pi_div_three]
    linarith
  specialize my_lemma this
  rw [my_lemma] at hx₂
  obtain ⟨k, hk⟩ := hx₂
  have hk₂: 0 ≤ k := by
    ring_nf at hk
    rw [←mul_add] at hk
    rw [hk, mul_pos_iff] at hx₁
    obtain (⟨r₁, r₂⟩ | ⟨r₁, r₂⟩) := hx₁
    · have : 0 < 3 * (k : ℝ) + 2 := by linarith
      norm_cast at this
      omega
    · absurd r₁
      simp
      linarith [pi_gt_three]
  rw [hk]
  simp
  rw [mul_nonneg_iff]
  simp
  apply Or.inl ⟨hk₂, by linarith [pi_gt_three]⟩
