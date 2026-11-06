import Mathlib

/-Among the numbers a,b, and c
one is positive, one is negative, and one is zero. Additionally, it is known that
|a| = b ^ 2 * (b - c).
Which of the numbers is positive, which is negative, and which is zero?-/

theorem algebra_291533 {a b c: ℝ} (h: |a| = b ^ 2 * (b - c))
(l: (a = 0 ∧ 0 < b ∧ c < 0) ∨ (a = 0 ∧ 0 < c ∧ b < 0) ∨
(b = 0 ∧ 0 < a ∧ c < 0) ∨ (b = 0 ∧ 0 < c ∧ a < 0) ∨
(c = 0 ∧ 0 < a ∧ b < 0) ∨ (c = 0 ∧ 0 < b ∧ a < 0)): c = 0 ∧ 0 < b ∧ a < 0 := by

  rcases l with l | l | l | l | l | l
  .
    -- a = 0
    rcases l with ⟨l1, l2, l3⟩
    simp [l1] at h
    rcases h with h | h
    .
      linarith
    .
      linarith

  .
    -- a = 0
    rcases l with ⟨l1, l2, l3⟩
    simp [l1] at h
    rcases h with h | h
    .
      linarith
    .
      linarith

  .
    -- b = 0
    rcases l with ⟨l1, l2, l3⟩
    simp [l1] at h
    simp [h] at l2

  .
    -- b = 0
    rcases l with ⟨l1, l2, l3⟩
    simp [l1] at h
    simp [h] at l3

  .
    -- c = 0
    rcases l with ⟨l1, l2, l3⟩
    simp [l1] at h
    have o: 0 ≤ b ^ 2 * b := by
      rw [← h]
      apply abs_nonneg
    have j: b ^ 2 * b ≤ 0 := by
      have r: 0 ≤ b ^ 2 := by
        apply sq_nonneg
      nlinarith
    have u: b ^ 2 * b = 0 := by linarith
    simp at u
    simp [u] at l3

  .
    -- c = 0
    exact l