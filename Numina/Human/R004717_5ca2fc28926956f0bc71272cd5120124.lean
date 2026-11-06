import Mathlib


theorem calculus_309058 (f : ℝ → ℝ) (m : ℝ)
  (f_def : f = fun x => x^3 - m * x^2 - x + 1):
  ( StrictMonoOn f (Set.Iic ((m - √(m^2+3))/3)) ∧
    StrictAntiOn f (Set.Icc ((m - √(m^2+3))/3) ((m + √(m^2+3))/3)) ∧
    StrictMonoOn f (Set.Ici ((m + √(m^2+3))/3))  )   ∧
  ( (∀x, deriv f x ≥ |x| - 7/4) ↔ m ∈ Set.Icc (-1) 1) := by

  have f_cont: Continuous f := by continuity
  have f_diff: Differentiable ℝ f := by continuity

  have f_deriv: deriv f = fun x => 3*x^2 - 2*m*x - 1 := by
    simp only [f_def, deriv_add_const']
    funext x
    rw [deriv_sub, deriv_sub, deriv_pow, deriv_const_mul, deriv_pow]
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', sub_left_inj, sub_right_inj]
    ring
    all_goals continuity

  set m1 := (m - √(m^2+3))/3 with m1_def
  set m2 := (m + √(m^2+3))/3 with m2_def
  have m1_lt_m2: m1 < m2 := by
    rw [m1_def, m2_def]
    have h1: 0 < √(m^2+3) := by
      refine Real.sqrt_pos_of_pos ?_
      linarith only [sq_nonneg m]
    have h2: -m < √(m^2+3) := by
      refine Real.lt_sqrt_of_sq_lt ?_
      simp
    apply div_lt_div₀ ?_ le_rfl ?_ (by norm_num)
    · linarith only [h1]
    · linarith only [h2]

  have f_deriv_eq (x:ℝ): deriv f x = 3 * (x - m1) * (x - m2) := by
    simp only [f_deriv]
    have h1: (x-m1)*(x-m2) = x^2 - (m1+m2)*x + m1*m2 := by ring
    have h2: m1+m2 = 2*m/3 := by ring
    have h3: m1*m2 = -1/3 := by
      rw [m1_def, m2_def, mul_div_left_comm, ← mul_div_assoc,
      ← mul_div_assoc, ← sq_sub_sq,
      Real.sq_sqrt (by linarith only [sq_nonneg m])]
      ring
    rw [mul_assoc 3 _ _, h1, h2, h3]
    ring

  have f_strictmono_1: StrictMonoOn f (Set.Iic m1) := by
    refine strictMonoOn_of_deriv_pos (convex_Iic _)
      (Continuous.continuousOn f_cont) ?_
    simp only [interior_Iic, Set.mem_Iio, f_deriv_eq]
    intro x hx
    apply mul_pos_of_neg_of_neg ?_ ?_
    · linarith only [hx]
    · linarith only [m1_lt_m2, hx]

  have f_strictanti: StrictAntiOn f (Set.Icc m1 m2) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (Continuous.continuousOn f_cont) ?_
    simp only [interior_Icc, Set.mem_Ioo, f_deriv_eq]
    rintro x ⟨hx1, hx2⟩
    apply mul_neg_of_pos_of_neg ?_ ?_
    · linarith only [hx1]
    · linarith only [hx2]

  have f_strictmono_2: StrictMonoOn f (Set.Ici m2) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici _)
      (Continuous.continuousOn f_cont) ?_
    simp only [interior_Ici, Set.mem_Ioi, f_deriv_eq]
    intro x hx
    apply mul_pos ?_ ?_
    · linarith only [hx, m1_lt_m2]
    · linarith only [hx]

  have part1: StrictMonoOn f (Set.Iic ((m - √(m^2+3))/3)) ∧
    StrictAntiOn f (Set.Icc ((m - √(m^2+3))/3) ((m + √(m^2+3))/3)) ∧
    StrictMonoOn f (Set.Ici ((m + √(m^2+3))/3)) := by
    rw [← m1_def, ← m2_def]
    exact ⟨f_strictmono_1, f_strictanti, f_strictmono_2⟩


  have heq {x:ℝ} (xne0: x ≠ 0):
    |x| * (3*|x|+3/(4*|x|)) = 3*|x|^2 + 3/4 := by
    have: |x| ≠ 0 := abs_ne_zero.mpr xne0
    field_simp only [this]
    ring

  have case_xpos {x:ℝ} (hx: 0 < x): (3*x^2-2*m*x-1 ≥ |x| - 7/4) ↔
    (3*|x| + 3 / (4*|x|) ≥ 1 + 2*m) := by
    have h1: (3*|x| + 3 / (4*|x|) ≥ 1 + 2*m) ↔
      |x| * (3*|x| + 3/(4*|x|)) ≥ |x| * (1 +2*m) := by
      refine Iff.symm (mul_le_mul_left ?_)
      exact abs_pos.mpr hx.ne'
    have h2: 2*m*x = 2*m*|x| := by
      rw [abs_of_pos hx]
    rw [h1, ← sq_abs, h2, heq hx.ne']
    constructor <;> intro hh <;> linarith only [hh]

  have case_xneg {x:ℝ} (hx: x < 0): (3*x^2-2*m*x-1 ≥ |x| - 7/4) ↔
    (3*|x| + 3/(4*|x|) ≥ 1 - 2*m) := by
    have h1: (3*|x| + 3 / (4*|x|) ≥ 1 - 2*m) ↔
      |x| * (3*|x| + 3/(4*|x|)) ≥ |x| * (1 - 2*m) := by
      refine Iff.symm (mul_le_mul_left ?_)
      exact abs_pos.mpr hx.ne
    have h2: 2*m*x = -2*m*|x| := by
      simp [abs_of_neg hx]
    rw [h1, ← sq_abs, h2, heq hx.ne]
    constructor <;> intro hh <;> linarith only [hh]

  have ineq {a b:ℝ} (ha: 0 < a) (hb: 0 < b):
    a + b ≥ 2 * √(a*b) := by
    replace ha := le_of_lt ha
    replace hb := le_of_lt hb
    rw [Real.sqrt_mul ha]
    nth_rw 1 [← Real.sq_sqrt ha, ← Real.sq_sqrt hb]
    rw [← mul_assoc]
    apply two_mul_le_add_sq

  replace ineq {x:ℝ} (xne0: x ≠ 0):
    3*|x| + 3/(4*|x|) ≥ 3 := by
    have h1: 3 * |x| + 3/(4*|x|) = 3 * (|x| + 1 / (4*|x|)) := by ring
    have h2: 0 < |x| := abs_pos.mpr xne0
    have h3: 0 < 1/(4*|x|) := by
      simp [xne0]
    specialize ineq h2 h3
    have h4: √(|x| * (1 / (4*|x|))) = 1/2 := by
      have hh1: |x| * (1 / (4*|x|)) = 1/4 := by simp [h2.ne']
      have hh2: √(1/4:ℝ) = 1/2 := by
        field_simp
        symm
        rw [Real.sqrt_eq_iff_mul_self_eq_of_pos]
        all_goals norm_num
      rw [hh1, hh2]
    rw [h4] at ineq
    rw [h1]
    linarith only [ineq]

  replace case_xpos: (∀x, 0 < x → 3*x^2-2*m*x-1 ≥ |x| - 7/4) ↔
    m ≤ 1 := by
    constructor <;> intro h
    · specialize h (1/2) (by norm_num)
      rw [abs_of_nonneg (by norm_num)] at h
      linarith only [h]
    · intro x hx
      rw [case_xpos hx]
      apply le_trans ?_ (ineq hx.ne')
      linarith only [h]

  replace case_xneg: (∀x, x < 0 → 3*x^2-2*m*x-1 ≥ |x| - 7/4) ↔
    -1 ≤ m := by
    constructor <;> intro h
    · specialize h (-1/2) (by norm_num)
      rw [abs_of_neg (by norm_num)] at h
      linarith only [h]
    · intro x hx
      rw [case_xneg hx]
      apply le_trans ?_ (ineq hx.ne)
      linarith only [h]

  have part2: (∀x, deriv f x ≥ |x| - 7/4) ↔ m ∈ Set.Icc (-1) 1 := by
    simp only [f_deriv, Set.mem_Icc, ← case_xpos, ← case_xneg]
    constructor <;> intro h
    · constructor <;> exact fun x _ => h x
    · intro x
      rcases (lt_trichotomy x 0) with xneg | xeq0 | xpos
      · apply h.left x xneg
      · rw [xeq0]
        norm_num
      · apply h.right x xpos

  exact ⟨part1, part2⟩