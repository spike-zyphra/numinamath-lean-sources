import Mathlib

theorem algebra_277726 (x y : ℤ) :
    x^2 + 2 * x * y + 3 * y^2 - 2 * x + y + 1 = 0 ↔ (x = 1 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨ (x = 3 ∧ y = -1) := by 
  constructor
  · -- Proof of the forward implication
    intro h
    have h1 : x^2 + 2 * x * y + 3 * y^2 - 2 * x + y + 1 = 0 := h
    have h2 : y ≥ -1 := by
      nlinarith [sq_nonneg (x + y - 1), sq_nonneg (y + 1)]
    have h3 : y ≤ 0 := by
      nlinarith [sq_nonneg (x + y - 1), sq_nonneg (y + 1)]
    have h4 : y = -1 ∨ y = 0 := by
      omega
    rcases h4 with (hy | hy)
    · -- Case y = -1
      have h5 : x^2 + 2 * x * (-1) + 3 * (-1)^2 - 2 * x + (-1) + 1 = 0 := by
        rw [show y = -1 by linarith [hy]] at h1
        linarith
      have h6 : (x - 1) * (x - 3) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h6) with h7 h8
      · -- Case x = 1
        have hx1 : x = 1 := by linarith
        have hy1 : y = -1 := by linarith [hy]
        simp [hx1, hy1]
        <;> tauto
      · -- Case x = 3
        have hx2 : x = 3 := by linarith
        have hy2 : y = -1 := by linarith [hy]
        simp [hx2, hy2]
        <;> tauto
    · -- Case y = 0
      have h6 : x^2 + 2 * x * 0 + 3 * (0:ℤ)^2 - 2 * x + (0:ℤ) + 1 = 0 := by
        rw [show y = 0 by linarith [hy]] at h1
        linarith
      have h7 : (x - 1)^2 = 0 := by
        nlinarith
      have h8 : x - 1 = 0 := by
        apply pow_eq_zero 
        exact h7
      have hx1 : x = 1 := by linarith
      have hy1 : y = 0 := by linarith [hy]
      simp [hx1, hy1]
      <;> tauto
  · -- Proof of the converse implication
    rintro (h | h | h)
    · -- First pair (1, 0)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Second pair (1, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Third pair (3, -1)
      rcases h with ⟨rfl, rfl⟩
      norm_num