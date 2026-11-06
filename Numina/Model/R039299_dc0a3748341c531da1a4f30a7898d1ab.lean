import Mathlib
theorem algebra_2656 (b : ℝ) :
    (∃ x, 1988 * x ^ 2 + b * x + 8891 = 0 ∧ 8891 * x ^ 2 + b * x + 1988 = 0) ↔
    b = 10879 ∨ b = - 10879 := by
  constructor
  · -- Assume there exists x such that both equations hold
    rintro ⟨x, ⟨h1, h2⟩⟩
    have h3 : 1988 * x ^ 2 + b * x + 8891 = 0 := h1
    have h4 : 8891 * x ^ 2 + b * x + 1988 = 0 := h2
    have eq1 : (1988 * x ^ 2 + b * x + 8891) - (8891 * x ^ 2 + b * x + 1988) = 0 := by
      linarith
    have eq2 : -6903 * x ^ 2 + 6903 = 0 := by
      nlinarith
    have eq2' : x ^ 2 = 1 := by
      nlinarith
    have h5 : x = 1 ∨ x = -1 := by
      have h6 : x ^ 2 - 1 = 0 := by
        linarith
      have h6' : (x - 1) * (x + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h6') with h7 h8
      · -- x - 1 = 0, so x = 1
        left
        linarith
      · -- x + 1 = 0, so x = -1
        right
        linarith
    rcases h5 with (h5 | h5)
    · -- x = 1
      rw [h5] at h1
      have h7 : b = -10879 := by
        linarith
      right
      linarith
    · -- x = -1
      rw [h5] at h1
      have h9 : b = 10879 := by
        linarith
      left
      linarith
  · -- Assume b = 10879 ∨ b = -10879
    rintro (hb | hb)
    · -- b = 10879
      use (-1)
      constructor
      · -- 1988 * (-1) ^ 2 + 10879 * (-1) + 8891 = 0
        rw [hb]
        norm_num
      · -- 8891 * (-1) ^ 2 + 10879 * (-1) + 1988 = 0
        rw [hb]
        norm_num
    · -- b = -10879
      use 1
      constructor
      · -- 1988 * 1 ^ 2 + (-10879) * 1 + 8891 = 0
        rw [hb]
        norm_num
      · -- 8891 * 1 ^ 2 + (-10879) * 1 + 1988 = 0
        rw [hb]
        norm_num