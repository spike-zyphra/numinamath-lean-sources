import Mathlib

theorem algebra_32026 {x1 x2 : ℝ} (hx : x1^5 - 55 * x1 + 21 = 0) (hx' : x2^5 - 55 * x2 + 21 = 0)
    (hx'' : x1 * x2 = 1) :
    ({x1, x2} : Set ℝ) = {(3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2} := by
  have h1 : x2 ≠ 0 := by
    by_contra h
    rw [h] at hx''
    nlinarith
  have h2 : x1 ≠ 0 := by
    by_contra h
    rw [h] at hx''
    nlinarith
  have h3 : x2 = 1 / x1 := by
    field_simp [h1, h2]
    nlinarith
  rw [h3] at hx'
  have h4 : x1^2 - 3 * x1 + 1 = 0 := by
    field_simp [h2] at hx' hx
    nlinarith [sq_nonneg (x1 ^ 2 - 1), sq_nonneg (x1 ^ 2 - 4), sq_nonneg (x1 - (3 + Real.sqrt 5) / 2), sq_nonneg (x1 - (3 - Real.sqrt 5) / 2), Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have h8 : x1 = (3 + Real.sqrt 5) / 2 ∨ x1 = (3 - Real.sqrt 5) / 2 := by
    have h5 : x1^2 - 3 * x1 + 1 = 0 := h4
    have h6 : (x1 - (3 + Real.sqrt 5) / 2) * (x1 - (3 - Real.sqrt 5) / 2) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- x1 = (3 + Real.sqrt 5) / 2
      left
      linarith
    · -- x1 = (3 - Real.sqrt 5) / 2
      right
      linarith
  cases h8 with
  | inl hx1 =>
    have hx2 : x2 = (3 - Real.sqrt 5) / 2 := by
      rw [hx1] at hx''
      field_simp [h1] at hx''
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Show that if a is in {x1, x2}, then it's in {(3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2}
      intro ha
      rcases ha with (rfl | rfl)
      · -- a = x1
        rw [hx1]
        left
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
      · -- a = x2
        rw [hx2]
        right
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
    · -- Show that if a is in {(3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2}, then it's in {x1, x2}
      intro ha
      rcases ha with (rfl | rfl)
      · -- a = (3 + Real.sqrt 5) / 2
        rw [hx1]
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
      · -- a = (3 - Real.sqrt 5) / 2
        rw [hx2]
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
  | inr hx1 =>
    have hx2 : x2 = (3 + Real.sqrt 5) / 2 := by
      rw [hx1] at hx''
      field_simp [h1] at hx''
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
    ext a
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Show that if a is in {x1, x2}, then it's in {(3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2}
      intro ha
      rcases ha with (rfl | rfl)
      · -- a = x1
        rw [hx1]
        right
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
      · -- a = x2
        rw [hx2]
        left
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
    · -- Show that if a is in {(3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2}, then it's in {x1, x2}
      intro ha
      rcases ha with (rfl | rfl)
      · -- a = (3 + Real.sqrt 5) / 2
        rw [hx2]
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }
      · -- a = (3 - Real.sqrt 5) / 2
        rw [hx1]
        all_goals norm_num
        <;> try { nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)] }