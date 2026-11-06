import Mathlib

theorem algebra_132398 (x y z : ℝ) :
    (x^2 + y^2 + 2 * x + 6 * y = -5 ∧ x^2 + z^2 + 2 * x - 4 * z = 8 ∧ y^2 + z^2 + 6 * y - 4 * z = -3) ↔
    (x = 1 ∧ y = -2 ∧ z = -1) ∨ (x = 1 ∧ y = -2 ∧ z = 5) ∨ (x = 1 ∧ y = -4 ∧ z = -1) ∨ (x = 1 ∧ y = -4 ∧ z = 5) ∨
    (x = -3 ∧ y = -2 ∧ z = -1) ∨ (x = -3 ∧ y = -2 ∧ z = 5) ∨ (x = -3 ∧ y = -4 ∧ z = -1) ∨ (x = -3 ∧ y = -4 ∧ z = 5) := by

  constructor
  · -- Assume the system of equations, need to prove the solutions
    rintro ⟨h1, h2, h3⟩
    have h4 : (x - 1) * (x + 3) = 0 := by
      nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 3), sq_nonneg (z - 2), sq_nonneg (x - 1), sq_nonneg (y + 2), sq_nonneg (z + 1), sq_nonneg (z - 5)]
    have hx : x = 1 ∨ x = -3 := by
      cases (mul_eq_zero.1 h4) with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        linarith
    rcases hx with hx | hx
    · -- Assume x = 1
      have hx1 : x = 1 := hx
      rw [hx1] at h1 h2
      have hy : (y + 2) * (y + 4) = 0 := by
        nlinarith
      have hy2 : y = -2 ∨ y = -4 := by
        cases (mul_eq_zero.1 hy) with
        | inl h =>
          left
          linarith
        | inr h =>
          right
          linarith
      rcases hy2 with hy | hy
      · -- Assume y = -2
        have hy2 : y = -2 := hy
        have hz : (z - 5) * (z + 1) = 0 := by
          rw [hy2] at h3
          nlinarith
        have hz5 : z = 5 ∨ z = -1 := by
          cases (mul_eq_zero.1 hz) with
          | inl h =>
            left
            linarith
          | inr h =>
            right
            linarith
        rcases hz5 with hz5 | hz5
        · -- Assume z = 5
          have hz5 : z = 5 := hz5
          tauto
        · -- Assume z = -1
          have hz1 : z = -1 := hz5
          tauto
      · -- Assume y = -4
        have hy4 : y = -4 := by linarith
        have hz : (z - 5) * (z + 1) = 0 := by
          rw [hy4] at h3
          nlinarith
        have hz5 : z = 5 ∨ z = -1 := by
          cases (mul_eq_zero.1 hz) with
          | inl h =>
            left
            linarith
          | inr h =>
            right
            linarith
        rcases hz5 with hz5 | hz5
        · -- Assume z = 5
          have hz5 : z = 5 := hz5
          tauto
        · -- Assume z = -1
          have hz1 : z = -1 := hz5
          tauto
    · -- Assume x = -3
      have hx3 : x = -3 := hx
      rw [hx3] at h1 h2
      have hy : (y + 2) * (y + 4) = 0 := by
        nlinarith
      have hy2 : y = -2 ∨ y = -4 := by
        cases (mul_eq_zero.1 hy) with
        | inl h =>
          left
          linarith
        | inr h =>
          right
          linarith
      rcases hy2 with hy | hy
      · -- Assume y = -2
        have hy2 : y = -2 := hy
        have hz : (z - 5) * (z + 1) = 0 := by
          rw [hy2] at h3
          nlinarith
        have hz5 : z = 5 ∨ z = -1 := by
          cases (mul_eq_zero.1 hz) with
          | inl h =>
            left
            linarith
          | inr h =>
            right
            linarith
        rcases hz5 with hz5 | hz5
        · -- Assume z = 5
          have hz5 : z = 5 := hz5
          tauto
        · -- Assume z = -1
          have hz1 : z = -1 := hz5
          tauto
      · -- Assume y = -4
        have hy4 : y = -4 := by linarith
        have hz : (z - 5) * (z + 1) = 0 := by
          rw [hy4] at h3
          nlinarith
        have hz5 : z = 5 ∨ z = -1 := by
          cases (mul_eq_zero.1 hz) with
          | inl h =>
            left
            linarith
          | inr h =>
            right
            linarith
        rcases hz5 with hz5 | hz5
        · -- Assume z = 5
          have hz5 : z = 5 := hz5
          tauto
        · -- Assume z = -1
          have hz1 : z = -1 := hz5
          tauto
  · -- Show that the solutions satisfy the system
    rintro (h | h | h | h | h | h | h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Second solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Third solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Fourth solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Fifth solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Sixth solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Seventh solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · -- Eighth solution
      rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num