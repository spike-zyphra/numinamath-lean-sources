import Mathlib

/- 21. (2004 China Western Mathematical Olympiad) Let $u$, $v$, $w$ be positive real numbers, satisfying the condition $u \sqrt{v w}+v \sqrt{w u}+w \sqrt{u v} \geqslant$ 1. Find the minimum value of $u+v+w$. -/
theorem inequalities_230072
  : IsLeast
    ((fun (u, v, w) => u + v + w) '' {(u, v, w) : ℝ × ℝ × ℝ | 0 < u ∧ 0 < v ∧ 0 < w ∧ 1 ≤ u * √(v * w) + v * √(w * u) + w * √(u * v)})
    √3
  := by
    constructor
    -- We can achieve the lower bound √3
    · simp only [Set.mem_image, Set.mem_setOf_eq]
      -- u = v = w = (√3) / 3
      refine ⟨⟨(√3) / 3, (√3) / 3, (√3) / 3⟩, ?_⟩
      simp only [Real.sqrt_pos, Nat.ofNat_pos, div_pos_iff_of_pos_left, true_and]
      refine ⟨?_, ?_⟩
      · ring_nf
        field_simp
        have sq_nine : √9 = 3 := by
          refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?_).mpr ?_
          linarith only
          linarith only
        rw [sq_nine]
        linarith only
      · ring_nf
    -- every other possible value is larger than or equal to √3
    · rw [mem_lowerBounds]
      simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists, forall_exists_index, and_imp]
      intro sum u v w u_pos v_pos w_pos bound sum_eq
      -- possible values are nonnegative
      have v_nonneg := le_of_lt v_pos
      have w_nonneg := le_of_lt w_pos
      have u_nonneg := le_of_lt u_pos

      -- consider the sum as just u + v + w
      subst sum_eq

      -- We have AM-GM for two variables: √(xy) ≤ (x + y) / 2
      have am_gm_simple : ∀ {x y}, (0 ≤ x) → (0 ≤ y) → √(x * y) ≤ (x + y) / 2 := by
        intro x y x_nonneg y_nonneg
        have half_nonneg : (0 : ℝ) ≤ 1 / 2 := by positivity
        -- Use weighted AM-GM with weights 1 / 2
        convert Real.geom_mean_le_arith_mean2_weighted half_nonneg half_nonneg x_nonneg y_nonneg (by linarith) using 1
        rw [Real.sqrt_mul x_nonneg]
        -- to the power of (1 / 2) is equal to square root
        congr
        exact Real.sqrt_eq_rpow x
        exact Real.sqrt_eq_rpow y
        ring

      -- Use AM-GM on each part of given bound
      have bound_1 : u * √(v * w) + v * √(w * u) + w * √(u * v)
        ≤ u * ((v + w) / 2) + v * ((w + u) / 2) + w * ((u + v) / 2) := by
          gcongr
          exact am_gm_simple v_nonneg w_nonneg
          exact am_gm_simple w_nonneg u_nonneg
          exact am_gm_simple u_nonneg v_nonneg

      -- then we know that 1 ≤ u * v + u * w + v * w
      have comb := le_trans bound bound_1
      ring_nf at comb

      -- then we can chain inequalities to get 3 ≤ (u + v + w) ^ 2
      have three_le_sum_sq : 3 ≤ (u + v + w) ^ 2 := by
        calc 3
        _ ≤ 3 * (u * v + v * w + w * u) := by
          -- use 1 ≤ u * v + u * w + v * w
          simp only [Nat.ofNat_pos, le_mul_iff_one_le_right]
          convert comb using 1
          ring
        -- split
        _ = (u * v + v * w + w * u) + 2 * (u * v + v * w + w * u) := by ring
        -- use AM-GM on products in left term
        _ ≤ ((u ^ 2 + v ^ 2) / 2 + (v ^ 2 + w ^ 2) / 2 + (w ^ 2 + u ^ 2) / 2)
          + 2 * (u * v + v * w + w * u) := by
            simp only [add_le_add_iff_right]
            have u_sq_nonneg : 0 ≤ u ^ 2 := by positivity
            have v_sq_nonneg : 0 ≤ v ^ 2 := by positivity
            have w_sq_nonneg : 0 ≤ w ^ 2 := by positivity
            gcongr
            exact le_of_eq_of_le (by field_simp) (am_gm_simple u_sq_nonneg v_sq_nonneg)
            exact le_of_eq_of_le (by field_simp) (am_gm_simple v_sq_nonneg w_sq_nonneg)
            exact le_of_eq_of_le (by field_simp) (am_gm_simple w_sq_nonneg u_sq_nonneg)
        -- simplify
        _ = (u + v + w) ^ 2 := by ring

      -- so √3 ≤ u + v + w
      refine le_of_le_of_eq (Real.sqrt_le_sqrt three_le_sum_sq) ?_
      exact Real.sqrt_sq (by positivity)