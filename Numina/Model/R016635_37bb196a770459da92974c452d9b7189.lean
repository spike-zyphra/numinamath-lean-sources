import Mathlib

theorem algebra_307405 {a b c : ℝ} (habc : a * b * c ≠ 0) (hsum : a + b + c = 2 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 2) :
    (1 - a) ^ 2 / (b * c) + (1 - b) ^ 2 / (c * a) + (1 - c) ^ 2 / (a * b) = 3 := by
  rcases hsum with ⟨h1, h2⟩
  have h3 : a ≠ 0 := by
    by_contra h
    have h4 : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have h4 : b ≠ 0 := by
    by_contra h
    have h5 : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have h5 : c ≠ 0 := by
    by_contra h
    have h6 : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction

  have h6 : a * b + b * c + c * a = 1 := by
    have h : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by ring
    rw [h1, h2] at h
    nlinarith

  have h7 : (1 - a) ^ 2 / (b * c) + (1 - b) ^ 2 / (c * a) + (1 - c) ^ 2 / (a * b) =
    ((1 - a) ^ 2 * a + (1 - b) ^ 2 * b + (1 - c) ^ 2 * c) / (a * b * c) := by
    field_simp [show b * c ≠ 0 by
      apply mul_ne_zero
      exact h4
      exact h5, show c * a ≠ 0 by
        apply mul_ne_zero
        exact h5
        exact h3, show a * b ≠ 0 by
          apply mul_ne_zero
          exact h3
          exact h4]
    ring

  rw [h7]

  have h8 : ((1 - a) ^ 2 * a + (1 - b) ^ 2 * b + (1 - c) ^ 2 * c) = 3 * (a * b * c) := by
    have hcubics : a ^ 3 + b ^ 3 + c ^ 3 = 2 + 3 * (a * b * c) := by
      have h : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = (a + b + c) * ((a ^ 2 + b ^ 2 + c ^ 2) - (a * b + b * c + c * a)) := by
        ring_nf
        <;> simp
        <;> ring
      rw [h1, h2, h6] at h
      nlinarith

    nlinarith [hcubics, sq_nonneg (a + b + c - 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

  rw [h8]

  field_simp [show a * b * c ≠ 0 by
    exact habc]
  <;> nlinarith