import Mathlib

theorem algebra_311209 {a : ℕ → ℝ} (ha1 : a 1 = 1)
    (han : ∀ n ≥ 2, a n = if Even n then a (n / 2) + 1 else 1 / a (n - 1)) :
    ∃ n, 0 < n ∧ a n = 30 / 19 := by
  have h2 : a 2 = 2 := by
    specialize han 2 (by norm_num)
    simp [Nat.even_iff, ha1] at han
    linarith
  have h3 : a 3 = 1 / 2 := by
    specialize han 3 (by norm_num)
    simp [Nat.even_iff, h2] at han
    linarith
  have h4 : a 4 = 3 := by
    specialize han 4 (by norm_num)
    simp [Nat.even_iff, h2] at han
    linarith
  have h5 : a 5 = 1 / 3 := by
    specialize han 5 (by norm_num)
    simp [Nat.even_iff, h4] at han
    linarith
  have h6 : a 6 = 3 / 2 := by
    specialize han 6 (by norm_num)
    simp [Nat.even_iff, h3] at han
    linarith
  have h7 : a 7 = 2 / 3 := by
    specialize han 7 (by norm_num)
    simp [Nat.even_iff, h6] at han
    linarith
  have h8 : a 8 = 4 := by
    specialize han 8 (by norm_num)
    simp [Nat.even_iff, h4] at han
    linarith
  have h9 : a 9 = 1 / 4 := by
    specialize han 9 (by norm_num)
    simp [Nat.even_iff, h8] at han
    linarith
  have h10 : a 10 = 4 / 3 := by
    specialize han 10 (by norm_num)
    simp [Nat.even_iff, h5] at han
    linarith
  have h11 : a 11 = 3 / 4 := by
    specialize han 11 (by norm_num)
    simp [Nat.even_iff, h10] at han
    linarith
  have h12 : a 12 = 5 / 2 := by
    specialize han 12 (by norm_num)
    simp [Nat.even_iff, h6] at han
    linarith
  have h13 : a 13 = 2 / 5 := by
    specialize han 13 (by norm_num)
    simp [Nat.even_iff, h12] at han
    linarith
  have h14 : a 14 = 5 / 3 := by
    specialize han 14 (by norm_num)
    simp [Nat.even_iff, h7] at han
    linarith
  have h15 : a 15 = 3 / 5 := by
    specialize han 15 (by norm_num)
    simp [Nat.even_iff, h14] at han
    linarith
  have h16 : a 16 = 5 := by
    specialize han 16 (by norm_num)
    simp [Nat.even_iff, h8] at han
    linarith
  -- Now using the above established values, compute further values.
  have h28 : a 28 = 8 / 3 := by
    have h28' : a 28 = a 14 + 1 := by
      specialize han 28 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h28']
    linarith [h14]
  -- Computing a_29
  have h29 : a 29 = 3 / 8 := by
    have h29' : a 29 = 1 / a 28 := by
      specialize han 29 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h29']
    rw [h28]
    norm_num
  -- Computing a_58
  have h58 : a 58 = 11 / 8 := by
    have h58' : a 58 = a 29 + 1 := by
      specialize han 58 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h58']
    rw [h29]
    norm_num
  -- Computing a_59
  have h59 : a 59 = 8 / 11 := by
    have h59' : a 59 = 1 / a 58 := by
      specialize han 59 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h59']
    rw [h58]
    norm_num
  -- Computing a_118
  have h118 : a 118 = 19 / 11 := by
    have h118' : a 118 = a 59 + 1 := by
      specialize han 118 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h118']
    rw [h59]
    norm_num
  -- Computing a_119
  have h119 : a 119 = 11 / 19 := by
    have h119' : a 119 = 1 / a 118 := by
      specialize han 119 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h119']
    rw [h118]
    norm_num
  -- Computing a_238
  have h238 : a 238 = 30 / 19 := by
    have h238' : a 238 = a 119 + 1 := by
      specialize han 238 (by norm_num)
      simp [Nat.even_iff] at han
      norm_num at han ⊢
      exact han
    rw [h238']
    rw [h119]
    norm_num
  use 238
  constructor
  · norm_num
  · exact h238