import Mathlib


theorem algebra_240130 (p q : ℕ) (hp : p = {x : ℝ | ∃ y : ℝ, (x ^ 2 + y ^ 2 - 2 * x) ^ 2 = 2 * (x ^ 2 + y ^ 2) ^ 2 ∧ y = 0}.ncard)
    (hq : q = {y : ℝ | ∃ x : ℝ, (x ^ 2 + y ^ 2 - 2 * x) ^ 2 = 2 * (x ^ 2 + y ^ 2) ^ 2 ∧ x = 0}.ncard) :
    100 * p + 100 * q = 400 := by

  have h_sq_sqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h_aux_root {x: ℝ}: x ^ 2 + 4 * x - 4 = 0 -> (x = (-2 + 2 * Real.sqrt 2) ∨ x = (-2 - 2 * Real.sqrt 2)) := by
    intro H
    have h3 : (x - (-2 + 2 * Real.sqrt 2)) * (x - (-2 - 2 * Real.sqrt 2)) = 0 := by
      ring_nf
      rw [h_sq_sqrt2, <-H]
      ring_nf
    rw [mul_eq_zero] at h3
    cases h3
    · left; linarith
    · right; linarith

  have h1 : {x : ℝ | ∃ y : ℝ, (x ^ 2 + y ^ 2 - 2 * x) ^ 2 = 2 * (x ^ 2 + y ^ 2) ^ 2 ∧ y = 0} = {0, -2 + 2 * Real.sqrt 2, -2 - 2 * Real.sqrt 2} := by
    ext x
    constructor
    · simp_intro h_eq
      ring_nf at h_eq
      have h_eq2 : x^2 * (x^2 + 4 * x - 4) = 0 := by linarith
      cases (mul_eq_zero.mp h_eq2) with
      | inl h2 => simp at h2; tauto
      | inr h2 => right; apply h_aux_root h2
    · rintro (rfl | rfl | rfl) <;> simp; try (ring_nf)
      · nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)]
      · nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < 2 by norm_num)]
      
  have hp3 : p = 3 := by
    rw [hp, h1, Set.ncard_eq_three]
    
    use 0; use -2 + 2 * Real.sqrt 2; use -2 - 2 * Real.sqrt 2
    apply And.intro _ (And.intro _ (And.intro _ _))
    · intro H
      symm at H
      simp [neg_add_eq_zero] at H
    · symm
      apply ne_of_lt
      simp
      apply lt_trans (b := 0) (by simp) (by simp)
    · intro H
      rw [<-add_right_inj 2, <-add_assoc, add_sub, <-neg_add_eq_zero] at H
      simp at H
    · simp
  have hq1 : q = 1 := by
    have h2 : {y : ℝ | ∃ x : ℝ, (x ^ 2 + y ^ 2 - 2 * x) ^ 2 = 2 * (x ^ 2 + y ^ 2) ^ 2 ∧ x = 0} = {0} := by
      ext y
      constructor
      · simp_intro h_eq
        ring_nf at h_eq
        symm at h_eq
        simpa [mul_right_eq_self₀] using h_eq
      · rintro rfl
        simp
    rw [h2] at hq
    rw [hq]
    simp

  calc
    100 * p + 100 * q = 100 * 3 + 100 * 1 := by rw [hp3, hq1]
    _ = 300 + 100 := by norm_num
    _ = 400 := by norm_num