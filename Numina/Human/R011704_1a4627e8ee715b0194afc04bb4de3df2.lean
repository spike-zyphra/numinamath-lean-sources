import Mathlib

open Real


/- Example 1 Given the equation about $x$: $\lg (x-1)+\lg (3-x)=\lg (a-x)$ has two distinct real roots,
find the range of values for $a$. -/
theorem algebra_148976 {a:ℝ}:
  {x:ℝ | (x-1 > 0 ∧ 3-x > 0 ∧ a-x > 0) ∧
  logb 10 (x-1) + logb 10 (3 - x) = logb 10 (a-x)}.ncard = 2 ↔
  3 < a ∧ a < 13/4 := by

  -- solve the original equation, transform it into a quadratic equation.
  have h1 {x:ℝ} (hx: x-1 > 0 ∧ 3-x > 0 ∧ a-x > 0):
    logb 10 (x-1) + logb 10 (3 - x) = logb 10 (a-x) ↔ (x-1)*(3-x) = a-x := by
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [← logb_mul hx1.ne' hx2.ne']
    -- if lg x = lg y, then x = y
    have := @logb_injOn_pos 10 (by norm_num)
    constructor
    · apply this ?_ ?_
      · simp only [Set.mem_Ioi, mul_pos, hx1, hx2]
      · simp only [Set.mem_Ioi, hx3]
    · intro h; rw [h]

  -- equation (x-1)(3-x) = a-x is equivalent to x^2 - 5x + (3+a) = 0
  have h2 {x:ℝ} (hx: x-1 > 0 ∧ 3-x > 0 ∧ a-x > 0):
    logb 10 (x-1) + logb 10 (3 - x) = logb 10 (a-x) ↔ 1*(x*x) + (-5)*x + (3+a) = 0 := by
    rw [h1 hx]
    constructor <;> intro h <;> linarith only [h]

  -- if this quadratic equation has two roots, then discriminant > 0, we find a < 13/4.
  -- besides, x > 1 follows from x-1>0 and a-x>0
  have h3 (h: {x:ℝ | (x-1 > 0 ∧ 3-x > 0 ∧ a-x > 0) ∧
    1*(x*x) + (-5)*x + (3+a) = 0 }.ncard = 2):
    3 < a ∧ a < 13/4 := by
    rw [Set.ncard_eq_two] at h
    rcases h with ⟨x1, x2, xne, h⟩
    have hx1: x1 ∈ ({x1,x2}: Set ℝ) := by simp
    simp only [← h, Set.mem_setOf_eq] at hx1
    have hx2: x2 ∈ ({x1,x2}: Set ℝ) := by simp
    simp only [← h, Set.mem_setOf_eq] at hx2
    obtain ⟨s,hs⟩ : ∃ s, discrim (1:ℝ) (-5) (3+a) = s*s := by
      rw [quadratic_eq_zero_iff_discrim_eq_sq (by norm_num)] at hx1
      use (2*1*x1 + -5)
      rw [hx1.right, pow_two]
    -- s ≠ 0, otherwise x1 = x2
    have snz: s ≠ 0 := by
      rintro seq
      rw [seq, mul_zero] at hs
      rw [quadratic_eq_zero_iff_of_discrim_eq_zero (by norm_num) hs] at hx1 hx2
      simp [hx1, hx2] at xne
    -- therefore discriminant > 0, we solve a < 13/4
    have alt: a < 13/4 := by
      have: discrim (1:ℝ) (-5) (3+a) > 0 := by
        rw [hs, ← pow_two]
        exact pow_two_pos_of_ne_zero snz
      dsimp only [discrim] at this
      linarith only [this]
    -- x-1 > 0, a -x > 0, therefore a > 1
    have agt: a > 1 := by
      linarith only [hx1.left]

    -- check more carefully, we find a > x1, a > x2. so a > the bigger one.
    -- and we can prove a > 3.
    let ss: ℝ := √(13-4*a)
    have sspos: 0 < ss := by
      apply sqrt_pos_of_pos ?_
      linarith only [alt]
    have slt: ss < √(3^2) := by
      rw [sqrt_lt_sqrt_iff (by linarith only [alt])]
      linarith only [agt]
    rw [sqrt_sq (by norm_num)] at slt
    have: discrim (1:ℝ) (-5) (3+a) = ss*ss := by
      rw [← pow_two, sq_sqrt (by linarith only [alt])]
      dsimp only [discrim]
      ring
    rw [quadratic_eq_zero_iff (by norm_num) this] at hx1 hx2
    simp only [neg_neg, mul_one] at hx1 hx2
    -- from a > x, we have a > (5+s)/2, and can find a tighter upperbound for a.
    have ha: a > (5 + ss)/2 := by
      have hax1 := hx1.left.right.right
      have hax2 := hx2.left.right.right
      replace hx1 := hx1.right
      replace hx2 := hx2.right
      rcases hx1 with hx1 | hx1
      <;> rcases hx2 with hx2 | hx2
      all_goals
        rw [hx1] at hax1
        rw [hx2] at hax2
        simp only [hx1, hx2, ne_eq, not_true_eq_false, ss] at xne
      <;> linarith only [hax1, hax2]
    replace ha: 2*a - 5 >  √(13-4*a) := by
      dsimp [ss] at ha
      linarith only [ha]
    replace ha: 13 - 4*a < (2*a-5)^2 := lt_sq_of_sqrt_lt ha
    replace ha: (a-3)*(a-1) > 0 := by linarith only [ha]
    -- then either a < 1 or a > 3, and a > 1 ensures a > 3.
    replace agt: a > 3 := by
      replace: a - 3 > 0 := by
        refine (pos_iff_pos_of_mul_pos ha).mpr ?_
        linarith only [agt]
      linarith only [this]
    exact ⟨agt, alt⟩



  constructor
  · intro h
    apply h3
    rw [← h]
    congr 1
    ext x
    simp only [gt_iff_lt, Set.mem_setOf_eq]
    constructor <;> rintro ⟨hl, hr⟩
    · simp only [hl, h2 hl, true_and, hr]
    · simp only [← h2 hl, hl, hr, true_and]
  · intro ha
    -- when 3 < a < 3, we solve x = (5 +- √(13-4a))/2.
    -- and we find these two x is between 1 and 3.
    let s: ℝ := √(13-4*a)
    have spos: 0 < s := by
      apply sqrt_pos_of_pos ?_
      linarith only [ha.right]
    have slt: s < √1 := by
      rw [sqrt_lt_sqrt_iff (by linarith only [ha.right])]
      linarith only [ha.left]
    simp only [sqrt_one] at slt
    have: discrim (1:ℝ) (-5) (3+a) = s*s := by
      rw [← pow_two, sq_sqrt (by linarith only [ha.right])]
      dsimp only [discrim]
      ring
    replace: {x:ℝ | (x-1 > 0 ∧ 3-x > 0 ∧ a-x > 0) ∧
      logb 10 (x-1) + logb 10 (3 - x) = logb 10 (a-x)} =
      {(5+s)/2, (5-s)/2} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
      constructor
      · rintro ⟨hl, hr⟩
        rw [h2 hl, quadratic_eq_zero_iff (by norm_num) this] at hr
        simpa only [neg_neg, mul_one] using hr
      · intro xeq
        have hx: x-1 > 0 ∧ 3-x > 0 ∧ a-x > 0 := by
          rcases xeq with xeq | xeq
          <;> rw [xeq] <;> split_ands
          all_goals linarith only [ha, spos, slt]
        simpa only [hx, h2 hx, true_and,
        quadratic_eq_zero_iff (by norm_num) this, neg_neg, mul_one] using xeq
    rw [this]
    apply Set.ncard_pair
    linarith only [spos]