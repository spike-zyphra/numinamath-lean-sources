import Mathlib

theorem algebra_244212 {x y : ℝ} (hy : y ≠ 0) :
    (4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2) =
    8 * abs y * (x ^ 2 + 1) ↔
    (2 * abs y + 1 / (2 * abs y)) * (x ^ 2 + 1 + 1 / (x ^ 2 + 1)) = 4 := by
  constructor
  · -- Forward direction: The original equation implies the second form
    intro h
    have h1 : abs y > 0 := by
      apply abs_pos.mpr
      exact hy
    have h2 : x ^ 2 + 1 > 0 := by
      nlinarith [sq_nonneg x]
    have h3 : 2 * abs y > 0 := by
      nlinarith
    have h4 : 2 * abs y * (x ^ 2 + 1) > 0 := by
      positivity
    have eq1 : (2 * abs y + 1 / (2 * abs y)) * (x ^ 2 + 1 + 1 / (x ^ 2 + 1)) = 4 := by
      have eq2 : (4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2) = 8 * abs y * (x ^ 2 + 1) := h
      have eq3 : 2 * abs y * (x ^ 2 + 1) > 0 := h4
      have eq4 : (2 * abs y + 1 / (2 * abs y)) * (x ^ 2 + 1 + 1 / (x ^ 2 + 1)) =
          ((4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2)) / (2 * abs y * (x ^ 2 + 1)) := by
        field_simp
        <;> ring_nf
        <;> field_simp [h1, h2]
        <;> ring
      rw [eq4]
      rw [eq2]
      field_simp
      <;> nlinarith [abs_nonneg y, sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 4)]
    exact eq1
  · -- Backward direction: The second form implies the original equation
    intro h
    have h1 : abs y > 0 := by
      apply abs_pos.mpr
      exact hy
    have h2 : x ^ 2 + 1 > 0 := by
      nlinarith [sq_nonneg x]
    have h3 : 2 * abs y > 0 := by
      nlinarith
    have h4 : 2 * abs y * (x ^ 2 + 1) > 0 := by
      positivity
    have eq1 : (4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2) =
        8 * abs y * (x ^ 2 + 1) := by
      have eq2 : (2 * abs y + 1 / (2 * abs y)) * (x ^ 2 + 1 + 1 / (x ^ 2 + 1)) = 4 := h
      have eq3 : (2 * abs y + 1 / (2 * abs y)) * (x ^ 2 + 1 + 1 / (x ^ 2 + 1)) =
          ((4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2)) / (2 * abs y * (x ^ 2 + 1)) := by
        field_simp
        <;> ring_nf
        <;> field_simp [h1, h2]
        <;> ring
      have eq4 : ((4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2)) / (2 * abs y * (x ^ 2 + 1)) = 4 := by
        linarith [eq2, eq3]
      have eq5 : (4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2) = 4 * (2 * abs y * (x ^ 2 + 1)) := by
        have h6 : ((4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2)) / (2 * abs y * (x ^ 2 + 1)) = 4 := eq4
        have h7 : 2 * abs y * (x ^ 2 + 1) > 0 := h4
        have h8 : (4 * y ^ 2 + 1) * (x ^ 4 + 2 * x ^ 2 + 2) = 4 * (2 * abs y * (x ^ 2 + 1)) := by
          field_simp at h6 ⊢
          all_goals nlinarith
        exact h8
      linarith [eq5]
    exact eq1