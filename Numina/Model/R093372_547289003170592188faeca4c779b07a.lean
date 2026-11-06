import Mathlib

theorem algebra_199181 {x y z : ℝ} (h1 : x * y = 2) (h2 : x * z = 3) (h3 : x ^ 2 + y ^ 2 = 5) :
    (x = 2 ∧ y = 1 ∧ z = 3 / 2) ∨ (x = -2 ∧ y = -1 ∧ z = -3 / 2) ∨
    (x = 1 ∧ y = 2 ∧ z = 3) ∨ (x = -1 ∧ y = -2 ∧ z = -3) := by
  have h4 : x ≠ 0 := by
    by_contra hx
    rw [hx] at h1 h2
    nlinarith
  have hy : y = 2 / x := by
    field_simp [h4]
    nlinarith
  have hz : z = 3 / x := by
    field_simp [h4]
    nlinarith
  have h5 : x ^ 2 + (2 / x) ^ 2 = 5 := by
    rw [hy] at h3
    nlinarith
  have h8 : x ^ 4 - 5 * x ^ 2 + 4 = 0 := by
    have h7 : x ^ 2 + (2 / x) ^ 2 = 5 := h5
    field_simp [h4] at h7 ⊢
    nlinarith [h7, sq_nonneg (x ^ 2 - 4), sq_nonneg (x ^ 2 - 1)]
  have h9 : (x ^ 2 - 1) * (x ^ 2 - 4) = 0 := by
    nlinarith [h8]
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- Case x^2 - 1 = 0, so x^2 = 1, so x = ±1
    have h12 : x ^ 2 = 1 := by linarith
    have h13 : x = 1 ∨ x = -1 := by
      rw [sq_eq_one_iff] at h12
      exact h12
    cases' h13 with h14 h15
    · -- x = 1
      have hy1 : y = 2 := by
        rw [h14] at h1
        nlinarith
      have hz1 : z = 3 := by
        rw [h14] at h2
        nlinarith
      simp [h14, hy1, hz1]
    · -- x = -1
      have hy2 : y = -2 := by
        rw [h15] at h1
        nlinarith
      have hz2 : z = -3 := by
        rw [h15] at h2
        nlinarith
      simp [h15, hy2, hz2]
  · -- Case x^2 - 4 = 0, so x^2 = 4, so x = ±2
    have h16 : x ^ 2 = 4 := by linarith
    have h17 : x = 2 ∨ x = -2 := by
      have h18 : x ^ 2 - 4 = 0 := by linarith
      have h19 : (x - 2) * (x + 2) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h19) with h20 h21
      · -- x - 2 = 0
        left
        linarith
      · -- x + 2 = 0
        right
        linarith
    cases' h17 with h22 h23
    · -- x = 2
      have hy3 : y = 1 := by
        rw [h22] at h1
        nlinarith
      have hz3 : z = 3 / 2 := by
        rw [h22] at h2
        nlinarith
      simp [h22, hy3, hz3]
    · -- x = -2
      have hy4 : y = -1 := by
        rw [h23] at h1
        nlinarith
      have hz4 : z = -3 / 2 := by
        rw [h23] at h2
        nlinarith
      simp [h23, hy4, hz4]