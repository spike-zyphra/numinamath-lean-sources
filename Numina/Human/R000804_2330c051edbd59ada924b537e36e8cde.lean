import Mathlib

open Real

/- How many integers $n$ satisfy the inequality $-8\pi\le n\le10\pi$? -/
theorem algebra_15922 :
  {n : ℤ | -8 * π ≤ n ∧ n ≤ 10 * π}.encard = 57 := by
  -- notice that π is between 3.14 and 3.15, so 8π between 25,26;  and 10 π between 31,32.
  -- in the new version of lean4, "pi_gt_314" is renamed as "pi_gt_d2"
  have pi_gt_d2 := pi_gt_314
  have pi_lt_d2 := pi_lt_315
  -- 8x3.14 = 25.12>25
  have h1: 25 < (8*π) := by
    have hh1:8*π > 8*3.14 := by linarith [pi_gt_d2]
    have hh2: 8*3.14 > (25:ℝ) := by norm_num
    exact gt_trans hh1 hh2
  -- 8x3.15 = 25.2<26
  have h2: 8*π < 26 := by
    have hh1: 8*π < 8*3.15 := by linarith [pi_lt_d2]
    have hh2: 8*3.15 < (26:ℝ) := by norm_num
    apply lt_trans hh1 hh2
  -- 10x3.15 = 31.5<32
  have h3: 10*π < 32 := by
    have hh1: 10*π < 10*3.15 := by linarith [pi_lt_d2]
    have hh2: 10*3.15 < (32:ℝ) := by norm_num
    apply lt_trans hh1 hh2
  -- 10x3.14 = 31.4>31
  have h4: 31 < 10*π := by
    have hh1: 10*π > 10*3.14 := by linarith [pi_gt_d2]
    have hh2: 10*3.14 > (31:ℝ) := by norm_num
    exact gt_trans hh1 hh2
  have h5: {n : ℤ | -8 * π ≤ n ∧ n ≤ 10 * π} =
    {n : ℤ | -25 ≤ n ∧ n ≤ 31} := by
    ext n; simp; constructor <;> intro h
    · constructor
      · have hh1 := h.left
        have hh2: -26 < -(8*π) := by
          exact neg_lt_neg_iff.mpr h2
        have hh3: (↑(-26:ℤ):ℝ) < n := by
          simp; exact gt_of_ge_of_gt hh1 hh2
        have hh4: -26 < n := by
          apply Int.cast_lt.mp hh3
        exact hh4
      · have hh1 := h.right
        have hh2: n < (32:ℝ) := by
          exact lt_of_le_of_lt hh1 h3
        have hh3: n < 32 := by
          apply Int.cast_lt.mp hh2
        exact Int.lt_add_one_iff.mp hh3
    · constructor
      · have hh1 := h.left
        have hh2: -(8*π) < -25 := by
          exact neg_lt_neg_iff.mpr h1
        have hh3: ↑(-25:ℤ) ≤ (n:ℝ) := by
          exact Int.cast_le.mpr hh1
        simp at hh3
        linarith [hh2, hh3]
      · have hh1 := h.right
        have hh2: n ≤ (↑(31:ℤ):ℝ) := by
          exact Int.cast_le.mpr hh1
        simp at hh2
        linarith [hh2, h4]
  -- so that set is just [-25, 31]
  rw [h5]
  have h6: {n : ℤ | -25 ≤ n ∧ n ≤ 31} = Set.Icc (-25) 31 := rfl
  rw [h6]
  -- and integer interval [a, b] contain b-a+1 integers. 31-(-25)+1 = 57, so set card is 57.
  rw [Set.encard]; simp