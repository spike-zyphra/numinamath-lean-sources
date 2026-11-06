import Mathlib

theorem algebra_208220 (a b c d : ℤ) :
    a * b - 2 * c * d = 3 ∧ a * c + b * d = 1 ↔
    (a = 1 ∧ b = 3 ∧ c = 1 ∧ d = 0) ∨
    (a = -1 ∧ b = -3 ∧ c = -1 ∧ d = 0) ∨
    (a = 3 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨
    (a = -3 ∧ b = -1 ∧ c = 0 ∧ d = -1) := by
  constructor
  · -- Assume the equations hold, prove they are one of the four cases given
    rintro ⟨h1, h2⟩
    have h3 : (a * b - 2 * c * d = 3) := h1
    have h4 : (a * c + b * d = 1) := h2
    have h5 : (a ^ 2 + 2 * d ^ 2) * (b ^ 2 + 2 * c ^ 2) = 11 := by
      nlinarith [sq_nonneg (a * d - b * c), sq_nonneg (a * c + b * d), sq_nonneg (a * b - 2 * c * d)]
    have h6 : a ^ 2 + 2 * d ^ 2 = 1 ∨ a ^ 2 + 2 * d ^ 2 = 11 := by
      have h6 : (a ^ 2 + 2 * d ^ 2) * (b ^ 2 + 2 * c ^ 2) = 11 := h5
      have h111 : (a ^ 2 + 2 * d ^ 2) ∣ 11 := by
        use (b ^ 2 + 2 * c ^ 2)
        all_goals nlinarith
      have h112 : (a ^ 2 + 2 * d ^ 2) > 0 := by
        nlinarith [sq_nonneg a, sq_nonneg d]
      have h112b : (a ^ 2 + 2 * d ^ 2) ≤ 11 := by
        exact Int.le_of_dvd (show 0 < (11 : ℤ) by norm_num) h111
      interval_cases k : (a ^ 2 + 2 * d ^ 2) <;> norm_num at *
    rcases h6 with h | h
    · -- Case $a^2 + 2 \cdot d^2 = 1$ (so $d = 0$ and $a = \pm 1$)
      have h7 : a ^ 2 + 2 * d ^ 2 = 1 := by
        omega
      have h8 : d = 0 := by
        nlinarith [sq_nonneg a, sq_nonneg d, sq_nonneg (a), sq_nonneg (d)]
      have h9 : a ^ 2 = 1 := by
        nlinarith [sq_nonneg a, sq_nonneg d, sq_nonneg (a), sq_nonneg (d)]
      have h10 : a = 1 ∨ a = -1 := by
        have h : a ^ 2 = 1 := by
          omega
        rw [sq_eq_one_iff] at h
        tauto
      have h7b : b ^ 2 + 2 * c ^ 2 = 11 := by
        nlinarith [h5, h7]
      rcases h10 with h11 | h12
      · -- Case $a = 1$
        have h13 : a = 1 := by
          omega
        have h15 : b = 3 := by
          nlinarith [h1, h8, h13, sq_nonneg (b), sq_nonneg (c)]
        have h16 : c = 1 := by
          nlinarith [h2, h13, h15, h8, sq_nonneg (c), sq_nonneg (b)]
        simp [h13, h15, h16, h8]
      · -- Case $a = -1$
        have h13 : a = -1 := by
          omega
        have h15 : b = -3 := by
          nlinarith [h1, h8, h13, sq_nonneg (b), sq_nonneg (c)]
        have h16 : c = -1 := by
          nlinarith [h2, h13, h15, h8, sq_nonneg (c), sq_nonneg (b)]
        simp [h13, h15, h16, h8]
    · -- Case $a^2 + 2 \cdot d^2 = 11$ (so $c = 0$ and $b = \pm 1$)
      have h7 : a ^ 2 + 2 * d ^ 2 = 11 := by
        omega
      have h7b : b ^ 2 + 2 * c ^ 2 = 1 := by
        nlinarith [h5, h7]
      have h11 : c = 0 := by
        nlinarith [sq_nonneg b, sq_nonneg c]
      have h12 : b = 1 ∨ b = -1 := by
        have h64 : b ^ 2 = 1 := by
          nlinarith [sq_nonneg (a), sq_nonneg (d), h7, h11, sq_nonneg b]
        rw [sq_eq_one_iff] at h64
        tauto
      rcases h12 with h13 | h13
      · -- Case $b = 1$
        have h14 : b = 1 := by
          omega
        have h15 : a = 3 := by
          nlinarith [h1, h14, h11, sq_nonneg (a), sq_nonneg (d)]
        have h17 : d = 1 := by
          nlinarith [sq_nonneg (a), sq_nonneg (d), h7, h15]
        simp [h15, h14, h11, h17]
      · -- Case $b = -1$
        have h14 : b = -1 := by
          omega
        have h15 : a = -3 := by
          nlinarith [h1, h14, h11, sq_nonneg (a), sq_nonneg (d)]
        have h17 : d = -1 := by
          nlinarith [sq_nonneg (a), sq_nonneg (d), h7, h15]
        simp [h15, h14, h11, h17]
  · -- Show that the given quadruples satisfy the equations
    rintro (h | h | h | h)
    · -- Case 1
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- Case 2
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- Case 3
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor
      · norm_num
      · norm_num
    · -- Case 4
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      constructor
      · norm_num
      · norm_num