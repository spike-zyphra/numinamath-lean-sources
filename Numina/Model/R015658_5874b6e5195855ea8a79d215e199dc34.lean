import Mathlib

theorem algebra_3841 (k : ℝ) :
    (∃ x y : ℝ, x > 0 ∧ y > 0 ∧ 2 * x - y = 2 ∧ y - k * x = k + 1) ↔
    -1 / 2 < k ∧ k < 2 := by
  constructor
  · -- Forward direction: If there exists a point (x, y) in the first quadrant, then -1/2 < k < 2
    rintro ⟨x, y, hx, hy, h1, h2⟩
    have eq1 : y = 2 * x - 2 := by
      linarith
    rw [eq1] at h2
    have eq2 : (2 - k) * x = k + 3 := by
      linarith
    by_cases h3 : 2 - k > 0
    · -- Assume $2 - k > 0$, so $k < 2$
      have hk1 : k < 2 := by 
        linarith
      have h4 : k + 3 > 0 := by
        nlinarith
      have h5 : 2 * k + 1 > 0 := by
        nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, h1, h2]
      constructor
      · linarith
      · linarith
    · -- Assume 2 - k ≤ 0
      have h4 : 2 - k ≤ 0 := by 
        linarith
      have eq4 : (2 - k) * x = k + 3 := eq2
      nlinarith [sq_nonneg (x - 1), sq_nonneg (k - 1)]
  · -- Backward direction: If -1/2 < k < 2, then there exists a point (x, y) in the first quadrant
    rintro ⟨hk1, hk2⟩
    have hk3 : 2 - k > 0 := by 
      linarith
    use (k + 3) / (2 - k)
    use (2 * (2 * k + 1)) / (2 - k)
    constructor
    · -- Show x > 0
      apply div_pos
      · -- Show k + 3 > 0
        linarith
      · -- Show 2 - k > 0
        linarith
    constructor
    · -- Show y > 0
      apply div_pos
      · -- Show 2 * (2 * k + 1) > 0
        linarith
      · -- Show 2 - k > 0
        linarith
    constructor
    · -- Show 2 * x - y = 2
      field_simp [(show (2 - k : ℝ) ≠ 0 by nlinarith)]
      <;> ring
    · -- Show y - k * x = k + 1
      field_simp [(show (2 - k : ℝ) ≠ 0 by nlinarith)]
      <;> ring