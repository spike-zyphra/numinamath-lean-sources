import Mathlib

/- Example \ Solve the equation $3 x^{3}-[x]=3$ -/
theorem algebra_277724 (x : ℝ) : 3 * x ^ 3 - ⌊x⌋ = 3 ↔ x = (4 / 3) ^ ((1 : ℝ) / 3) := by
  -- 1 < (4/3)^(1/3) this fact is used multiple times so proved first
  have h₁ : (1:ℤ) ≤ ((4:ℝ)/3)^((1:ℝ)/3) := by
    norm_cast
    calc
      (1:ℝ) = 1 ^((1:ℝ)/3) := by simp
      _ ≤ ((4:ℝ)/3)^((1:ℝ)/3) := by
        refine Real.rpow_le_rpow ?_ ?_ ?_ <;> norm_num
  constructor <;> rintro h
    -- left to right direction proof
    -- first prove a lemma that |⌊x⌋| ≤ |x| + 1
  . have floor_abs (x: ℝ) : |⌊x⌋| ≤ |x| + 1 := by
      -- we'll prove -(|x|+1) ≤ ⌊x⌋ ≤ |x|+1, each of these we'll prove by utilizing a ≤ |b| iff a < b or b < -a
      have hx₁ : ⌊x⌋ ≤ |x| + 1 := by
        have : ⌊x⌋ - 1 ≤ |x| := by
          apply le_abs.mpr
          left
          suffices ⌊x⌋ ≤ x by linarith
          exact Int.floor_le x
        linarith
      have hx₂ : -(|x| + 1) ≤ ⌊x⌋ := by
        have : -⌊x⌋ - 1 ≤ |x| := by
          apply le_abs.mpr
          right
          suffices x < ⌊x⌋ + 1 by linarith
          exact Int.lt_floor_add_one x
        linarith
      push_cast
      exact abs_le.mpr ⟨hx₂, hx₁⟩
    -- next first show that |x| < 2 has to happen
    have hx_bound: |x| < 2 := by
      -- by contradiction, if |x| ≤ 2 then |3x^3 - ⌊x⌋| ≥ 3|x|^3 - |x| -1 > 3
      by_contra hx_bound
      simp at hx_bound
      have := calc
        3 = |3| := by norm_num
        _ = |3 * x^3 - ⌊x⌋| := by rw [h]
        _ ≥ |3 * x^3| - |⌊x⌋| := by
          have := abs_sub_abs_le_abs_sub (3*x^3:ℝ) (⌊x⌋)
          norm_cast at *
        _ = 3 * |x|^3 - |⌊x⌋| := by rw [abs_mul, abs_pow]; simp
        _ ≥ 3 * |x|^3 - (|x| + 1) := by
          gcongr
          exact floor_abs _
        _ = |x| * (3*|x|^2 - 1) - 1 := by ring
        _ ≥ 2 * (3 * 2^2 -1) - 1 := by
          gcongr
        _ > 3 := by norm_num
      norm_num at this
    -- so we have bounds for ⌊x⌋ which is (-3, 2)
    have hx_bound : -2 < x ∧ x < 2 := by exact abs_lt.mp hx_bound
    have : -3 < ⌊x⌋ := by
      have := calc
        -3 = -2 - 1 := by norm_num
        _ < x - 1 := by gcongr; exact hx_bound.left
        _ < ⌊x⌋ := by exact Int.sub_one_lt_floor x
      norm_cast at this
    have : ⌊x⌋ < 2 := by
      have := calc
        ⌊x⌋ ≤ x := by exact Int.floor_le x
        _ < 2 := by exact hx_bound.right
      norm_cast at this
    have h3_odd : Odd 3 := by use 1; norm_num
    -- so we can do case work on ⌊x⌋
    interval_cases hx: ⌊x⌋
    all_goals (have hx_bound := Int.lt_floor_add_one x; rw [hx] at hx_bound; norm_num at hx_bound)
    all_goals ring_nf at h
    -- for ⌊x⌋ = -2, -1, 3x^3 is positive, impossible
    repeat
      have : x^3 > 0 := by linarith
      have := (Odd.pow_pos_iff h3_odd).mp this
      linarith
    -- for ⌊x⌋ = 0, x = 1, again impossible
    . have : x^3 = 1^3 := by linarith
      have : x = 1 := by
        refine (pow_left_inj₀ ?_ ?_ ?_).mp this
        any_goals norm_num
        calc
          (0:ℝ) = ⌊x⌋ := by exact_mod_cast hx.symm
          _ ≤ x := by exact Int.floor_le x
      linarith
    -- for ⌊x⌋ = 1, we get x^3 = 4/3 and hence target is proved
    . have hx' : x^3 = 4/3 := by linarith
      have : 4/3 = ((4/3:ℝ)^(1/3:ℝ))^3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        positivity
      rw [this] at hx'
      refine (pow_left_inj₀ ?_ ?_ ?_).mp hx'
      . calc
          (0:ℝ) ≤ 1 := by norm_num
          _ = ⌊x⌋ := by exact_mod_cast hx.symm
          _ ≤ x := by exact Int.floor_le x
      . linarith
      . norm_num
    -- for right to left, plug in (4/3)^(1/3) and show that it's floor is really 1 by bouding it in [1, 2)
  . rw [h, ← Real.rpow_natCast, ← Real.rpow_mul]
    pick_goal 2; norm_num
    norm_num
    have h₂ : ((4:ℝ)/3)^((1:ℝ)/3) < (1:ℤ) + 1 := by
      norm_num; norm_cast
      calc
        ((4:ℝ)/3)^((1:ℝ)/3) < (2^(3:ℝ))^((1:ℝ)/3) := by
          refine Real.rpow_lt_rpow ?_ ?_ ?_
          all_goals norm_num
        _ = 2 := by
          rw [← Real.rpow_mul]
          all_goals norm_num
    have : ⌊((4:ℝ)/3)^((1:ℝ)/3)⌋ = 1 := by exact_mod_cast Int.floor_eq_iff.mpr ⟨h₁, h₂⟩
    rw [this]
    norm_num