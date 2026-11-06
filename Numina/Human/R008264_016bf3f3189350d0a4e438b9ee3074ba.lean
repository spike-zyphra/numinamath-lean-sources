import Mathlib

open Real Set
open scoped BigOperators

set_option maxHeartbeats 250000

/- Let $x_1, x_2, \dots , x_6$ be non-negative real numbers such that $x_1 +x_2 +x_3 +x_4 +x_5 +x_6 =1$, and $x_1 x_3 x_5 +x_2 x_4 x_6 \ge \frac{1}{540}$. Find the maximum value of
\[x_1 x_2 x_3 + x_2 x_3 x_4 +x_3 x_4 x_5 +x_4 x_5 x_6 +x_5 x_6 x_1 +x_6 x_1 x_2.\] -/
theorem algebra_22256:
  IsGreatest {z:ℝ | ∃(x1 x2 x3 x4 x5 x6:ℝ), z = x1*x2*x3 + x2*x3*x4 + x3*x4*x5 +
    x4*x5*x6 + x5*x6*x1 + x6*x1*x2 ∧ x1 + x2 + x3 + x4 + x5 + x6 = 1 ∧
    (0 ≤ x1 ∧ 0 ≤ x2 ∧ 0 ≤ x3 ∧ 0 ≤ x4 ∧ 0 ≤ x5 ∧ 0 ≤ x6) ∧
    x1*x3*x5 + x2*x4*x6 ≥ 1/540} (19/540:ℝ) := by
  -- by AM-GM, if a,b,c are nonnegative, then a b c ≤ (a + b + c) ^ 3 / 27
    have h1(a b c: ℝ)(ha: 0 ≤ a)(hb: 0 ≤ b)(hc: 0 ≤ c): a * b* c ≤
    (a+b+c)^3 / 27 := by
        have h_am_gm : (a * b * c) ^ (1 / 3 :ℝ) ≤ (a + b + c) / 3 := by
            have hh1: (a * b * c) ^ (1 / 3 : ℝ) =
                a^(1/3:ℝ) * b^(1/3:ℝ) * c^(1/3 :ℝ) := by
                rw [← mul_rpow ha hb]
                have hab: 0 ≤ a * b := mul_nonneg ha hb
                rw [← mul_rpow hab hc]
            have hh2: (a+b+c)/3 = (1/3:ℝ)*a + (1/3:ℝ)*b + (1/3:ℝ)*c := by
                ring
            rw [hh1, hh2]
            have hh3: 0 ≤ (1/3:ℝ) := by norm_num
            have hh4: (1/3:ℝ)+ (1/3:ℝ) + (1/3:ℝ) = 1 := by norm_num
            apply geom_mean_le_arith_mean3_weighted hh3 hh3 hh3
                ha hb hc hh4
        have hh1: (a*b*c) = ((a*b*c)^(1/3:ℝ))^3 := by
            have tt1: ((a*b*c)^(1/3:ℝ))^3 = ((a*b*c)^(1/3:ℝ))^(3:ℝ) := by
                rw [← rpow_natCast]; simp
            have tt2: ((a*b*c)^(1/3:ℝ))^(3:ℝ) = (a*b*c)^((1/3:ℝ)*(3:ℝ)) := by
                rw [rpow_mul]
                apply mul_nonneg (mul_nonneg ha hb) hc
            have tt3: (a*b*c)^((1/3:ℝ)*(3:ℝ)) = (a*b*c) := by simp
            rw [tt1, tt2, tt3]
        have hh2: (a+b+c)^3/27 = ((a+b+c)/3)^3 := by
            ring
        rw [hh1, hh2]
        apply pow_le_pow_left
        have: 0 ≤ a*b*c := by
            apply mul_nonneg (mul_nonneg ha hb) hc
        exact rpow_nonneg this (1 / 3)
        exact h_am_gm
    rw [IsGreatest, upperBounds]; simp; constructor
    -- show that reach 19/540 when AM-GM take equal. 
    focus
        -- later we will prove, for AM-Gm take equal, we should have
        -- x1+x4 = x2+x5 = x3+x6
        -- a possible solution is x1=x3 = 3/10, x5 = 1/60,
        -- x2 = 19/60, x4 = 1/30, x6 = 1/30. so we use these values here.
        use 3/10, 19/60, 3/10, 1/30, 1/60, 1/30
        constructor
        ring
        ring_nf; simp
        norm_num
    -- show that 19/540 is an upper bound
    focus
        intro b x1 x2 x3 x4 x5 x6 b_def hx
            hx1 hx2 hx3 hx4 hx5 hx6
        -- to simplify, let a = x1x3x5+x2x4x6, and b = z
        let a := x1*x3*x5 + x2*x4*x6
        have a_def: a = x1*x3*x5 + x2*x4*x6 := rfl
        rw [← a_def]
        intro age
        -- notice that a+b = (x1+x4)(x2+x5)(x3+x6)
        have h2: a + b = (x1+x4)*(x2+x5)*(x3+x6) := by
            rw [a_def, b_def]; ring
        -- apply AM-GM to a+b
        have h3: a+b ≤ (1/27:ℝ) := by
            have tt1: 0 ≤ x1+x4 := by
                apply add_nonneg hx1 hx4
            have tt2: 0 ≤ x2+x5 := by
                apply add_nonneg hx2 hx5
            have tt3: 0 ≤ x3+x6 := by
                apply add_nonneg hx3 hx6
            have am_gm := h1 (x1+x4) (x2+x5) (x3+x6) tt1 tt2 tt3
            have tt4: (x1+x4) + (x2+x5) + (x3+x6) = 1 := by
                rw [← hx]; ring
            rw [← h2, tt4] at am_gm
            norm_num at am_gm; exact am_gm
        -- since a+b ≤ 1/27, we have b ≤ 1/27 - a
        have h4: b ≤ 1/27 - a := by linarith [h3]
        -- since a ≥ 1/540, we have 1/27 - a ≤ 1/27 - 1/540
        have h5: 1/27 - a ≤ 1/27 - (540:ℝ)⁻¹ := by
          exact tsub_le_tsub_left age (1 / 27)
        have h6: (19/540:ℝ) = 1/27 - (540:ℝ)⁻¹ := by field_simp; ring
        rw [h6]
        apply le_trans h4 h5