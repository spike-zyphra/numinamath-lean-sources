import Mathlib
set_option maxHeartbeats 0

open Complex EuclideanGeometry

/-Let $A B C D$ be a quadrilateral such that $\angle A B C=\angle C D A=90^{\circ}$, and $B C=7$. Let $E$ and $F$ be on $B D$ such that $A E$ and $C F$ are perpendicular to $B D$. Suppose that $B E=3$. Determine the product of the smallest and largest possible lengths of $D F$.-/
theorem geometry_609095 {Dst : Set ℝ} (hDst : Dst = {t | ∃ A B C D E F : ℂ, t = dist D F ∧ D = 0
    ∧ (∃ c : ℝ, 0 < c ∧ C = c) ∧ 0 < B.im ∧ (∃ a : ℝ, 0 < a ∧ A = a * I) ∧
    ∠ A B C = Real.pi / 2 ∧ dist B C = 7 ∧ dist B E = 3 ∧ ∠ B E D = Real.pi ∧
    ∠ B F D = Real.pi ∧ ∠ A E D = Real.pi / 2 ∧ ∠ C F D = Real.pi / 2})
    (hmax : IsGreatest Dst M) (hmin : IsLeast Dst L) : M * L = 9 := by
-- It suffices to show the distance set is a singleton ${3}$
  suffices : Dst = {3}
  · rw [this] at hmax hmin
    rw [IsGreatest.isGreatest_iff_eq isGreatest_singleton] at hmax
    rw [IsLeast.isLeast_iff_eq isLeast_singleton] at hmin
    rw [← hmax, ← hmin]; norm_num
-- Split the goal to a universal statement and an existential statement
  rw [hDst, Set.eq_singleton_iff_unique_mem, and_comm]; constructor
  -- To prove the universal statement, we first introduce variables and assumptions
  · simp; intro t A B C D E F ht hD c cpos hC imBpos a apos hA
    intro ang1 d1 d2 ang2 ang3 ang4 ang5; rw [ht]
  -- Rewrite all the angles to `Complex.arg` and remove the absolute values
    simp [angle] at ang1 ang2 ang3 ang4 ang5
    rw [angle_eq_abs_arg] at ang1 ang2 ang3 ang4 ang5
    rw [abs_eq, or_comm] at ang1 ang2 ang3 ang4 ang5
    rcases ang2 with h|ang2
    · suffices : -Real.pi < ((B - E) / (D - E)).arg
      · linarith only [this, h]
      apply neg_pi_lt_arg
    rcases ang3 with h|ang3
    · suffices : -Real.pi < ((B - F) / (D - F)).arg
      · linarith only [this, h]
      apply neg_pi_lt_arg
  -- Rewrite the conditions on `Complex.arg` to conditions on `Complex.im` or `Complex.re`
    rw [arg_eq_pi_iff] at ang2 ang3
    rcases ang2 with ⟨reneg1, ang2⟩; rcases ang3 with ⟨reneg2, ang3⟩
    rw [arg_eq_pi_div_two_iff, arg_eq_neg_pi_div_two_iff] at ang1 ang4 ang5
    rw [← and_or_left] at ang1 ang4 ang5
    rcases ang1 with ⟨ang1, imne1⟩; rcases ang4 with ⟨ang4, imne2⟩
    rcases ang5 with ⟨ang5, imne3⟩
  -- Simplify the assumptions to equations about `Complex.im` and `Complex.re`
    rw [div_im, div_sub_div_same] at ang2 ang3
    rw [div_re, div_add_div_same] at ang1 ang4 ang5
    rw [div_eq_zero_iff, or_comm] at ang1 ang2 ang3 ang4 ang5
    rcases ang1 with h|ang1
    · simp at h; rw [sub_eq_zero] at h
      rw [← h] at imBpos; simp [hC] at imBpos
    rcases ang2 with h|ang2
    · simp at h; simp [h] at reneg1
    rcases ang3 with h|ang3
    · simp at h; simp [h] at reneg2
    rcases ang4 with h|ang4
    · simp at h; simp [h] at reneg1
    rcases ang5 with h|ang5
    · simp at h; simp [h] at reneg2
    simp [hA, hC, hD] at ang1 ang2 ang3 ang4 ang5
  -- Rewrite and simplify the `dist`'s in `d1`, `d2` and the goal
    simp [dist_eq, abs_eq_sqrt_sq_add_sq, hC] at d1 d2
    rw [Real.sqrt_eq_iff_eq_sq] at d1 d2
    simp [dist_eq, abs_eq_sqrt_sq_add_sq, hD]
    rw [Real.sqrt_eq_iff_eq_sq]; clear d1
    ring_nf at ang1 ang2 ang3 ang4 ang5 d2
    rw [add_assoc, neg_add_eq_zero] at ang4 ang5
    rw [sub_eq_zero] at ang2 ang3
    rw [add_assoc, ← ang4] at d2
  -- Denote the ratio $B.re/B.im$ by $k$ and prove that $k$ is nonzero
    let k := B.re / B.im; have kne0 : k ≠ 0 := by
      intro h; dsimp [k] at h; rw [div_eq_zero_iff] at h
      rcases h with h|h
      · simp [h] at ang1; rw [neg_add_eq_zero] at ang1
        rw [pow_two] at ang1; apply mul_right_cancel₀ at ang1
        suffices : A - B = 0; simp [this] at imne1
        rw [Complex.ext_iff]; simp [hA, h, ang1]
        positivity
      linarith only [imBpos, h]
  -- Rewrite `ang2` and `ang3` in terms of $k$
    have hk : B.re = k * B.im := by
      dsimp [k]; rw [div_mul_cancel₀]; positivity
    replace ang2 : E.re = k * E.im := by
      dsimp [k]; rw [div_mul_eq_mul_div, eq_div_iff, ang2]
      ring; positivity
    rw [ang2, show E.im^2+(k*E.im)^2 = (1+k^2)*E.im*E.im by ring] at ang4
    apply mul_right_cancel₀ at ang4; replace ang3 : F.re = k * F.im := by
      dsimp [k]; rw [div_mul_eq_mul_div, eq_div_iff, ang3]
      ring; positivity
    rw [ang3, show F.im^2+(k*F.im)^2 = (1+k^2)*F.im*F.im by ring] at ang5
    rw [← mul_assoc] at ang5; apply mul_right_cancel₀ at ang5
    rw [← eq_div_iff] at ang5
  -- Substitute `ang4`, `ang5` and `hk` in `ang1`, then factorize the equation in `ang1`
    rw [ang4, ang5, hk] at ang1; field_simp at ang1
    simp [show -(k*B.im*((1+k^2)*F.im))+((k*B.im)^2-(1+k^2)*E.im*B.im)*k+B.im^2*k =
    k*B.im*(B.im-E.im-F.im)*(k^2+1) by ring, or_assoc] at ang1
    rcases ang1 with _|h|h|h; contradiction
    -- Discuss all possible cases and find that $B.im = E.im + F.im$ is the only possible case
    · linarith only [h, imBpos]
    · rw [sub_sub, sub_eq_zero] at h
    -- Prove that $B.re = E.re + F.re$ and substitute this together with `h`, `ang2` and `ang4` at `d2`, the final goal follows
      have : B.re = E.re + F.re := by rw [hk, ang2, ang3, h]; ring
      rw [this, h, ang2, ang4] at d2; ring_nf at d2
      rw [d2]; norm_num
    suffices : 0 < k ^ 2 + 1
    · linarith [this, h]
  -- Finish the rest trivial goals, mainly checking positivities
    any_goals positivity
    · intro h; simp [h] at ang3
      suffices : D - F = 0; simp [this] at reneg2
      rw [Complex.ext_iff]; simp [hD, h, ang3]
    · intro h; simp [h] at ang2
      suffices : D - E = 0; simp [this] at reneg1
      rw [Complex.ext_iff]; simp [hD, h, ang2]
    · intro h; rw [abs_eq, or_comm] at ang3
      rcases ang3 with h'|ang3
      · suffices : -Real.pi < ((B - F) / (D - F)).arg
        · linarith only [this, h']
        apply neg_pi_lt_arg
      rw [arg_eq_pi_iff] at ang3; rcases ang3 with ⟨reneg1, ang3⟩
      rw [div_im, div_sub_div_same, div_eq_zero_iff, or_comm] at ang3
      rcases ang3 with h|ang3
      · simp at h; simp [h] at reneg1
      rw [sub_eq_zero, hC] at h; simp [hD, ← h] at ang3
      rcases ang3 with h|h
      · linarith only [h, imBpos]
      linarith only [cpos, h]; positivity
    any_goals intro h; simp [h] at ang3; linarith only [ang3, Real.pi_pos]
    · intro h; rw [abs_eq, or_comm] at ang2
      rcases ang2 with h'|ang2
      · suffices : -Real.pi < ((B - E) / (D - E)).arg
        · linarith only [this, h']
        apply neg_pi_lt_arg
      rw [arg_eq_pi_iff] at ang2; rcases ang2 with ⟨reneg1, ang2⟩
      rw [div_im, div_sub_div_same, div_eq_zero_iff, or_comm] at ang2
      rcases ang2 with h|ang3
      · simp at h; simp [h] at reneg1
      rw [sub_eq_zero, hA] at h; rw [div_re, div_add_div_same] at reneg1
      simp [hD, ← h] at ang3 reneg1; rcases ang3 with h|h
      · rw [abs_eq, arg_eq_pi_div_two_iff, arg_eq_neg_pi_div_two_iff] at ang1
        rw [← and_or_left] at ang1; rcases ang1 with ⟨ang1, imne1⟩
        rw [div_re, div_add_div_same, div_eq_zero_iff, or_comm] at ang1
        rcases ang1 with h|ang1
        · simp at h; simp [h] at imne1
        simp [hA, h, hC] at ang1; rcases ang1 with h'|h'
        · rw [← neg_eq_zero, neg_sub] at h'
          simp [h'] at reneg1
        linarith only [h', imBpos]; positivity
      linarith only [h, apos]; positivity
    any_goals intro h; simp [h] at ang2; linarith only [ang2, Real.pi_pos]
    · intro h; rw [sub_eq_zero] at h
      rw [h] at ang4; linarith only [ang4, ang2, Real.pi_pos]
    intro h; rw [sub_eq_zero] at h
    rw [h] at ang5; linarith only [ang3, ang5, Real.pi_pos]
-- In order to show the existential goal, we need to construct a configuration satisfying all the desired properties
-- The configuration we choose here is two isomorphic right triangles $ADC$ and $ABC$
  simp; use 21*√10/20*I, 18/7+12/7*√10*I, 7, 0, 9/7+6/7*√10*I, 9/7+6/7*√10*I
  simp [dist_eq, abs_eq_sqrt_sq_add_sq]; split_ands
  · rw [mul_pow]; norm_num
    symm; rw [Real.sqrt_eq_iff_eq_sq]; all_goals norm_num
  · use 7; simp
  · use 21 * √10 / 20; simp
  · simp [angle]; rw [angle_eq_abs_arg, abs_eq]
    rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff]
    rw [← and_or_left]; constructor
    · rw [div_re, div_add_div_same, div_eq_zero_iff]
      left; simp; field_simp; ring_nf; norm_num
    apply lt_or_gt_of_ne; intro h; symm at h
    rw [div_im, div_sub_div_same, div_eq_zero_iff] at h
    rcases h with h|h
    · simp at h; rw [← neg_eq_zero] at h; ring_nf at h
      suffices : 0 < √10 * (147 / 20)
      · linarith only [this, h]
      positivity
    simp [Complex.ext_iff] at h; positivity
    all_goals simp [Complex.ext_iff]
  · rw [mul_pow]; norm_num
    rw [Real.sqrt_eq_iff_eq_sq]; all_goals norm_num
  · ring_nf; norm_num
    rw [Real.sqrt_eq_iff_eq_sq]; all_goals norm_num
  · rw [angle_eq_pi_iff_sbtw, Sbtw, Wbtw, affineSegment]
    split_ands
    · use 1/2; norm_num
      simp [AffineMap.lineMap]; ring
    simp [Complex.ext_iff]; intro h; linarith only [h]
    simp [Complex.ext_iff]
  · simp [angle]; rw [angle_eq_abs_arg, abs_eq]
    rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff]
    rw [← and_or_left]; constructor
    · rw [div_re, div_add_div_same, div_eq_zero_iff]
      left; simp; field_simp; ring_nf; norm_num
    apply lt_or_gt_of_ne; intro h; symm at h
    rw [div_im, div_sub_div_same, div_eq_zero_iff] at h
    rcases h with h|h
    · simp at h; rw [← neg_eq_zero] at h; ring_nf at h
      suffices : 0 < √10 * (147 / 20)
      · linarith only [this, h]
      positivity
    simp [Complex.ext_iff] at h; positivity
    all_goals simp [Complex.ext_iff]
  simp [angle]; rw [angle_eq_abs_arg, abs_eq]
  rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff]
  rw [← and_or_left]; constructor
  · rw [div_re, div_add_div_same, div_eq_zero_iff]
    left; simp; field_simp; ring_nf; norm_num
  apply lt_or_gt_of_ne; intro h; symm at h
  rw [div_im, div_sub_div_same, div_eq_zero_iff] at h
  rcases h with h|h
  · simp at h; rw [← neg_eq_zero] at h; ring_nf at h
    suffices : 0 < √10 * (147 / 20)
    · linarith only [this, h]
    positivity
  simp [Complex.ext_iff] at h; positivity
  all_goals simp [Complex.ext_iff]