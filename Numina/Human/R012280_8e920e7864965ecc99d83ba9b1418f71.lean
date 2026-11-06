import Mathlib


/--
Problem statement (Main theorem of this file):
If $a$, $b$, $c$ are all real numbers, then $p$: $ac<{}0$, is (   ) for $q$: the equation $a{{x}^{2}}+bx+c=0$ has one positive root and one negative root.

A: Necessary but not sufficient condition

B: Sufficient and necessary condition

C: Sufficient but not necessary condition

D: Neither sufficient nor necessary condition

Solution:
If $ac<{}0$, then $a\ne 0$, and $\Delta ={{b}^{2}}-4ac>0$, the product of the two roots $\frac{c}{a}<{}0$, so the sufficiency holds;

If $a{{x}^{2}}+bx+c=0$ has one positive root and one negative root, then $\frac{c}{a}<{}0$, thus $ac<{}0$, so the necessity also holds.

-/

-- we write the simp form of vieta's formula as a lemma
lemma vieta_formula {p q x1 x2: ℝ} (ne: x1 ≠ x2) (h1: x1 ^ 2 + p * x1 + q = 0) (h2: x2 ^ 2 + p * x2 + q = 0):
    x1 + x2 = -p ∧ x1 * x2 = q := by

  have h: (x1 - x2) * (x1 + x2 + p) = 0 := by nlinarith
  replace ne: ¬ x1 - x2 = 0 := by
    by_contra! i
    replace i: x1 = x2 := by linarith
    simp [i] at ne
  simp [ne] at h
  constructor
  . linarith
  . have f: (x1 + x2) ^ 2 - 2 * (x1 * x2) + p * (x1 + x2) + 2 * q = 0 := by
      nlinarith
    replace h: x1 + x2 = -p := by linarith
    simp [h] at f
    nlinarith

theorem my_favorite_theorem (a b c : ℝ) (p q : ℝ → ℝ → ℝ → Prop)
    (hp : p = fun a b c => a * c < 0)
    (hq : q = fun a b c => ∃! (x: ℝ × ℝ) , 0 < x.1 ∧ a * x.1 ^ 2 + b * x.1 + c = 0 ∧ x.2 < 0 ∧ a * x.2 ^ 2 + b * x.2 + c = 0)
    : (p a b c → q a b c) ∧ (q a b c → p a b c) := by
    constructor
    . intro h1
      simp [hp] at h1
      simp [hq]
      have h_a_ne_zero: a ≠ 0 := by
        by_contra h
        rw [h] at h1
        simp at h1

      have h_ca: c / a < 0 := by
        rw [←mul_lt_mul_right (sq_pos_of_ne_zero h_a_ne_zero)]
        have : c / a * a ^ 2 = a * c := by field_simp; ring
        rw [this]
        linarith

      have h_delta1 :  0 ≤ √((b / (2 * a)) ^ 2 - c / a) := by
        have : (b / (2 * a)) ^ 2 >= 0 := by nlinarith
        have : c / a < 0 := by linarith
        have : (b / (2 * a)) ^ 2 - c / a >= 0 := by nlinarith
        exact Real.sqrt_nonneg _

      have h_delta2 :  0 ≤ (b / (2 * a)) ^ 2 - c / a := by nlinarith


      use (-b/(2*a) + √((b/(2*a))^2-c/a), -b/(2*a) - √((b/(2*a))^2-c/a))

      constructor
      . constructor
        . simp
          suffices -(-b / (2 * a)) < √((b / (2 * a)) ^ 2 - c / a) by
            linarith

          apply lt_of_mul_self_lt_mul_self₀ h_delta1
          have : -(-b / (2 * a)) * -(-b / (2 * a)) = (b / (2 * a)) ^ 2 := by ring
          rw [this, Real.mul_self_sqrt h_delta2]
          linarith

        . simp
          constructor
          . field_simp
            ring_nf

            have : 0 ≤ a * b ^ 2 * a⁻¹ ^ 3 * (1 / 4) - a ^ 2 * c * a⁻¹ ^ 3 := by
              have : a * b ^ 2 * a⁻¹ ^ 3 * (1 / 4) - a ^ 2 * c * a⁻¹ ^ 3 = (b / (2 * a)) ^ 2 - c / a:= by field_simp; ring
              rw [this]
              linarith

            rw [Real.sq_sqrt this]
            field_simp
            ring_nf

          . constructor
            . apply lt_of_mul_self_lt_mul_self₀ h_delta1
              have : -b / (2 * a) * (-b / (2 * a)) = (b / (2 * a)) ^ 2 := by ring
              rw [this, Real.mul_self_sqrt h_delta2]
              linarith
            . field_simp
              ring_nf
              have : 0 ≤ a * b ^ 2 * a⁻¹ ^ 3 * (1 / 4) - a ^ 2 * c * a⁻¹ ^ 3 := by
                have : a * b ^ 2 * a⁻¹ ^ 3 * (1 / 4) - a ^ 2 * c * a⁻¹ ^ 3 = (b / (2 * a)) ^ 2 - c / a:= by field_simp; ring
                rw [this]
                linarith

              rw [Real.sq_sqrt this]
              field_simp
              ring_nf

      . intro x ⟨ hx1, h_x1_eq, hx2, h_x2_eq ⟩
        replace h_x1_eq: x.1 ^ 2 + (b/a)*x.1+(c/a)=0  := by
          field_simp
          rw [← h_x1_eq]
          ring_nf
        replace h_x2_eq: x.2 ^ 2 + (b/a)*x.2+(c/a)=0  := by
          field_simp
          rw [← h_x2_eq]
          ring_nf

        have h_x1_x2_ne: x.1 ≠ x.2 := by
          by_contra h
          rw [h] at hx1
          linarith

        have ⟨h_x1_x2_sum, h_x1_x2_prod⟩ := vieta_formula h_x1_x2_ne h_x1_eq h_x2_eq

        have : (x.1-x.2)^2 = (x.1+x.2)^2 - 4 * x.1 * x.2 := by ring

        have : (x.1 - x.2)^2 = (b/a)^2 - 4 * c / a := by
          rw [h_x1_x2_sum,mul_assoc, h_x1_x2_prod] at this
          rw [this]
          ring_nf

        have h_x1_x2_sub : x.1 - x.2 = √ ((b/a)^2 - 4 * c / a) := by
          rw [← this, Real.sqrt_sq]
          linarith

        have h_x1: x.1 = -b / (2 * a) + √((b / a) ^ 2 - 4 * c / a) / 2:= by
          have : 2 * x.1 = (x.1+x.2) + (x.1-x.2) := by ring
          rw [h_x1_x2_sum, h_x1_x2_sub] at this
          rw [mul_comm, ← eq_div_iff_mul_eq (by norm_num: (2 : ℝ) ≠ 0)] at this
          rw [this]
          ring_nf

        have h_x2: x.2 = -b / (2 * a) - √((b / a) ^ 2 - 4 * c / a) / 2:= by
          have : 2 * x.2 = (x.1+x.2) - (x.1-x.2) := by ring
          rw [h_x1_x2_sum, h_x1_x2_sub] at this
          rw [mul_comm, ← eq_div_iff_mul_eq (by norm_num: (2 : ℝ) ≠ 0)] at this
          rw [this]
          ring_nf

        have h_x1' : x.1 = -b / (2 * a) + √((b / (2 * a)) ^ 2 - c / a) := by
          have : √((b / a) ^ 2 - 4 * c / a) / 2 = √((b / (2 * a)) ^ 2 - c / a) := by
            have : 2 = √4 := by
              rw [(by norm_num: (4: ℝ) = 2^2), Real.sqrt_sq]
              positivity
            nth_rw 1 [this]
            rw [← Real.sqrt_div']
            field_simp
            ring_nf
            linarith
          rw [← this]
          exact h_x1

        have h_x2' : x.2 = -b / (2 * a) - √((b / (2 * a)) ^ 2 - c / a) := by
          have : √((b / a) ^ 2 - 4 * c / a) / 2 = √((b / (2 * a)) ^ 2 - c / a) := by
            have : 2 = √4 := by
              rw [(by norm_num: (4: ℝ) = 2^2), Real.sqrt_sq]
              positivity
            nth_rw 1 [this]
            rw [← Real.sqrt_div']
            field_simp
            ring_nf
            linarith
          rw [← this]
          exact h_x2

        rw [← h_x1', ← h_x2']

    . intro h1
      simp [hp]
      simp [hq] at h1

      rcases h1 with ⟨x, ⟨⟨h_x1_pos, ⟨h_x1_eq, ⟨h_x2_neg, h_x2_eq⟩⟩⟩, hy⟩⟩
      by_cases h_a_zero: a = 0
      . rw [h_a_zero] at h_x1_eq
        rw [h_a_zero] at h_x2_eq
        simp at h_x1_eq
        simp at h_x2_eq
        by_cases h_b_zero: b = 0
        . rw [h_b_zero] at h_x1_eq
          simp at h_x1_eq
          rw [h_a_zero, h_b_zero] at hy
          simp at hy
          have hy_1:= hy 1 (-1)
          have hy_2:= hy 2 (-2)
          simp at hy_1
          simp at hy_2
          have hy_11:= hy_1 h_x1_eq
          have hy_21:= hy_2 h_x1_eq
          rw [← hy_11] at hy_21
          simp at hy_21

        . have h_x1 : x.1 = -c / b := by field_simp; linarith
          have h_x2 : x.2 = -c / b := by field_simp; linarith
          linarith
      . -- case a ≠ 0
        replace h_x1_eq: x.1 ^ 2 + (b/a)*x.1+(c/a)=0  := by
          field_simp
          rw [← h_x1_eq]
          ring_nf
        replace h_x2_eq: x.2 ^ 2 + (b/a)*x.2+(c/a)=0  := by
          field_simp
          rw [← h_x2_eq]
          ring_nf

        have h_x1_x2_ne: x.1 ≠ x.2 := by
          by_contra h
          rw [h] at h_x1_pos
          linarith

        have ⟨h_x1_x2_sum, h_x1_x2_prod⟩ := vieta_formula h_x1_x2_ne h_x1_eq h_x2_eq

        have h_ca: c / a < 0 := by
          have : x.1 * x.2 < 0 := by
            rw [mul_comm]
            exact mul_neg_of_neg_of_pos h_x2_neg h_x1_pos
          linarith

        have h_ac: a * c < 0 := by
          rw [←mul_lt_mul_right (sq_pos_of_ne_zero h_a_zero)] at h_ca
          have : c / a * (a^2) = c * a := by field_simp; ring
          rw [this] at h_ca
          linarith

        exact h_ac
