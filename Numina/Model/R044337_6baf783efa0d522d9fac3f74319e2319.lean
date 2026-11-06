import Mathlib

theorem algebra_298827 (c : ℝ) :
    (c > -1 ∧ c < 3 / 2) ↔ ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ x - y = 2 ∧ c * x + y = 3 := by
  constructor
  · -- Forward direction: If c is in (-1, 3/2), then there exists (x, y) in the first quadrant
    rintro ⟨hc1, hc2⟩
    use 5 / (1 + c), (3 - 2 * c) / (1 + c)
    constructor
    · -- Show x > 0
      apply div_pos
      · norm_num
      · -- Show 1 + c > 0
        linarith
    constructor
    · -- Show y > 0
      apply div_pos
      · -- Show 3 - 2 * c > 0
        linarith
      · -- Show 1 + c > 0
        linarith
    constructor
    · -- Show x - y = 2
      field_simp [(show 1 + c ≠ 0 by linarith)]
      <;> ring
    · -- Show c * x + y = 3
      field_simp [(show 1 + c ≠ 0 by linarith)]
      <;> ring
  · -- Backward direction: If (x, y) exists in the first quadrant, then c is in (-1, 3/2)
    rintro ⟨x, y, hx, hy, heq1, heq2⟩
    constructor
    · -- Show c > -1
      by_contra h
      push_neg at h
      have h1 : c + 1 ≤ 0 := by linarith
      have h2 : x * (c + 1) = 5 := by
        have h_y : y = x - 2 := by linarith
        rw [h_y] at heq2
        nlinarith
      have h3 : x * (c + 1) ≤ 0 := by
        nlinarith
      nlinarith
    · -- Show c < 3 / 2
      by_contra h
      push_neg at h
      have h_y : y = x - 2 := by linarith
      rw [h_y] at heq2
      nlinarith