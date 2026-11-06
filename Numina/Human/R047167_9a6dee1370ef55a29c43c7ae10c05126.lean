import Mathlib


/- $x, y, z$ are positive reals with sum $3$.
Show that $$6 < \sqrt{2x+3} + \sqrt{2y+3} + \sqrt{2z+3}\le 3\sqrt5$$ -/
theorem inequalities_43775 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 3) :
    6 <  √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ∧
    √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ≤ 3 * √5 := by

  -- use geom mean ≤ arith mean deal with left
  -- and arith mean ≤ power arith mean deal with right.

  set w : ℕ → ℝ := fun n => 1/3 with w_def
  set zz: ℕ → ℝ := fun n =>
    match n with
    | 0 => √(2*x+3)
    | 1 => √(2*y+3)
    | 2 => √(2*z+3)
    | n+3 => 0
    with zz_def
  have hw1: ∀i ∈ Finset.range 3, w i ≥ 0 := by simp [w_def]
  have hw2: ∑i ∈ Finset.range 3, w i = 1 := by simp [w_def]
  have znng: ∀ i ∈ Finset.range 3, 0 ≤ zz i := by
    intro i hi
    obtain (rfl | rfl | rfl): i = 0 ∨ i = 1 ∨ i = 2 := by
      simp at hi
      clear * - hi
      decide +revert
    all_goals simp [zz_def]

  have hp: 1 ≤ (2:ℝ) := by norm_num

  have nng1: 0 ≤ 2*x+3 := by positivity
  have nng2: 0 ≤ 2*y+3 := by positivity
  have nng3: 0 ≤ 2*z+3 := by positivity

  -- arith mean ≤ power arith mean
  -- (a+b+c)/3 ≤ (a^2/3 + b^2/3 + c^2/3)^(1/2)
  have ineq1 := Real.arith_mean_le_rpow_mean
    (Finset.range 3) w zz hw1 hw2 znng hp

  -- simplify
  replace ineq1: √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ≤ 3 * √5 := by
    simp only [w_def, zz_def, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, Real.rpow_two] at ineq1
    rw [Real.sq_sqrt nng1, Real.sq_sqrt nng2, Real.sq_sqrt nng3] at ineq1
    have: 1/3 * (2*x+3) + 1/3 * (2*y+3) + 1/3 * (2*z+3) =
      1/3 * (2*(x+y+z)+9) := by ring
    rw [this, hsum] at ineq1
    norm_num [← Real.sqrt_eq_rpow] at ineq1
    linarith only [ineq1]

  -- arith mean ≥ geom mean
  -- 1/3 (a + b + c) ≥ (abc)^(1/3)
  have ineq2: (1/3) * √(2 * x + 3) + (1/3) * √(2 * y + 3) + (1/3) * √(2 * z + 3) ≥
    (√(2 * x + 3))^(1/3:ℝ) * (√(2 * y + 3))^(1/3:ℝ) * (√(2 * z + 3))^(1/3:ℝ) := by
    have h1: 0 ≤ (1/3:ℝ) := by norm_num
    have h2: 0 ≤ √(2*x+3) := by simp
    have h3: 0 ≤ √(2*y+3) := by simp
    have h4: 0 ≤ √(2*z+3) := by simp
    apply Real.geom_mean_le_arith_mean3_weighted h1 h1 h1 h2 h3 h4 (by norm_num)

  -- simplify, that inequality is ... ≥ 3 x 9^(1/3) > 3 x 8^(1/3) = 6.
  replace ineq2: √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) > 6 := by
    simp only [← Real.mul_rpow, Real.sqrt_nonneg] at ineq2
    rw [← Real.mul_rpow (by positivity) (by positivity)] at ineq2
    simp only [Real.sqrt_eq_rpow, ← Real.mul_rpow, nng1, nng2] at ineq2
    rw [← Real.mul_rpow (Left.mul_nonneg nng1 nng2) nng3] at ineq2
    -- (2x+3)(2y+3)(2z+3) = 27 + 18(x+y+z) + ... > 27 + 18(x+y+z) = 81
    have: (2*x+3) * (2*y+3) * (2*z+3) =
      27 + 18 * (x+y+z) + 12 * (x*y+y*z+x*z) + 8*(x*y*z) := by ring
    rw [this, hsum] at ineq2
    have h1: 27+18*3 + 12 * (x*y+y*z+x*z) + 8*(x*y*z) ≥ 81 := by
      have hh1: 27 + 18*3 = 81 := by norm_num
      have hh2: x*y+y*z+x*z ≥ 0 := by positivity
      have hh3: x*y*z ≥ 0 := by positivity
      linarith only [hh1, hh2, hh3]
    simp only [← Real.sqrt_eq_rpow] at ineq2
    have h2: 1/3 * √(2*x+3) + 1/3 * √(2*y+3) + 1/3 * √(2*z+3) ≥
      (√81)^(1/3:ℝ) := by
      have: √(27+18*3 + 12 * (x*y+y*z+x*z) + 8*(x*y*z)) ≥ √81 := by
        exact Real.sqrt_le_sqrt h1
      replace: (√(27+18*3 + 12 * (x*y+y*z+x*z) + 8*(x*y*z)))^(1/3:ℝ)
        ≥ (√81)^(1/3:ℝ) := by
        apply (Real.rpow_le_rpow_iff ?_ ?_ ?_).mpr this
        all_goals simp
      apply le_trans this ineq2
    -- so that inequality > (√81)^(1/3) = 9^(1/3) > 2.
    replace ineq2: √(2 * x + 3) + √(2 * y + 3) + √(2 * z + 3) ≥
      3 * 9^(1/3:ℝ) := by
      have: √(81:ℝ) = 9 := by
        have: (81:ℝ) = 9^2 := by norm_num
        rw [this, Real.sqrt_sq (by norm_num)]
      rw [this] at h2
      linarith only [h2]
    have h3: (9:ℝ)^(1/3:ℝ) > 8^(1/3:ℝ) := by
      have: (8:ℝ) < 9 := by norm_num
      apply (Real.rpow_lt_rpow_iff ?_ ?_ ?_).mpr this
      all_goals norm_num
    have h4: (8:ℝ)^(1/3:ℝ) = 2 := by
      have: (8:ℝ) = 2^(3:ℝ) := by norm_num
      rw [this, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4] at h3
    linarith only [ineq2, h3]

  exact ⟨ineq2, ineq1⟩