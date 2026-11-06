import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_123854 {C1 C2 C3 C4 : Set (ℝ × ℝ)}
  (hC1 : C1 = {(x, y) | x^2 - y^2 = x/(x^2 + y^2)})
  (hC2 : C2 = {(x, y) | 2*x*y + y/(x^2 + y^2) = 3})
  (hC3 : C3 = {(x, y) | x^3 - 3*x*y^2 + 3*y = 1})
  (hC4 : C4 = {(x, y) | 3*y*x^2 - 3*x - y^3 = 0}) :
  C1 ∩ C2 = C3 ∩ C4 := by
  ext ⟨x, y⟩
  simp [hC1, hC2, hC3, hC4]
  constructor
  · -- Assume (x, y) ∈ C1 ∩ C2; prove (x, y) ∈ C3 ∩ C4
    rintro ⟨h1, h2⟩
    have h3 : x^2 + y^2 > 0 := by
      by_contra h
      push_neg at h
      have h11 : x^2 + y^2 = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, h]
      have h22 : x = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, h11]
      have h33 : y = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, h11]
      rw [h22, h33] at h1 h2
      norm_num at h1 h2
    have eq1 : (x^2 - y^2) * (x^2 + y^2) = x := by
      have h4 : x^2 + y^2 ≠ 0 := by linarith
      field_simp [h4] at h1
      nlinarith
    have eq2 : (2 * x * y) * (x^2 + y^2) + y = 3 * (x^2 + y^2) := by
      have h4 : x^2 + y^2 ≠ 0 := by linarith
      field_simp [h4] at h2
      nlinarith
    constructor
    · -- Prove C3: x^3 - 3xy^2 + 3y = 1
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (x - 1), sq_nonneg (y + x), sq_nonneg (x * y)]
    · -- Prove C4: 3yx^2 - 3x - y^3 = 0
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (x - 1), sq_nonneg (y + x), sq_nonneg (x * y)]
  · -- Assume (x, y) ∈ C3 ∩ C4; prove (x, y) ∈ C1 ∩ C2
    rintro ⟨h1, h2⟩
    have h3 : x^2 + y^2 > 0 := by
      by_contra h
      push_neg at h
      have h11 : x^2 + y^2 = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, h]
      have h22 : x = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, h11]
      have h33 : y = 0 := by
        nlinarith [sq_nonneg x, sq_nonneg y, h11]
      rw [h22, h33] at h1 h2
      norm_num at h1 h2
    have eq1 : (x^2 - y^2) * (x^2 + y^2) = x := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (x - 1), sq_nonneg (y + x), sq_nonneg (x * y)]
    have eq2 : (2 * x * y) * (x^2 + y^2) + y = 3 * (x^2 + y^2) := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (y - 1), sq_nonneg (x - 1), sq_nonneg (x - 1), sq_nonneg (y + x), sq_nonneg (x * y)]
    constructor
    · -- Prove h1 : x^2 - y^2 = x/(x^2 + y^2)
      have h4 : x^2 + y^2 ≠ 0 := by linarith
      field_simp [h4]
      <;> nlinarith
    · -- Prove h2 : 2 * x * y + y/(x^2 + y^2) = 3
      have h4 : x^2 + y^2 ≠ 0 := by linarith
      field_simp [h4]
      <;> nlinarith