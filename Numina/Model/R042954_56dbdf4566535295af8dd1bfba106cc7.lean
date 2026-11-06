import Mathlib


theorem algebra_13017 (a b c d : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
    (hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d) (hroots : {x | x^4 + 2 * x^3 - 13 * x^2 - 14 * x + 24 = 0} = {a, b, c, d}) :
    a^2 + b^2 + c^2 + d^2 = 30 := by

  have h1 : a^4 + 2 * a^3 - 13 * a^2 - 14 * a + 24 = 0 := by
    have ha1 : a ∈ {x | x^4 + 2 * x^3 - 13 * x^2 - 14 * x + 24 = 0} := by
      rw [hroots]
      simp
    simpa using ha1

  have h2 : b^4 + 2 * b^3 - 13 * b^2 - 14 * b + 24 = 0 := by
    have hb1 : b ∈ {x | x^4 + 2 * x^3 - 13 * x^2 - 14 * x + 24 = 0} := by
      rw [hroots]
      simp
    simpa using hb1

  have h3 : c^4 + 2 * c^3 - 13 * c^2 - 14 * c + 24 = 0 := by
    have hc1 : c ∈ {x | x^4 + 2 * x^3 - 13 * x^2 - 14 * x + 24 = 0} := by
      rw [hroots]
      simp
    simpa using hc1

  have h4 : d^4 + 2 * d^3 - 13 * d^2 - 14 * d + 24 = 0 := by
    have hd1 : d ∈ {x | x^4 + 2 * x^3 - 13 * x^2 - 14 * x + 24 = 0} := by
      rw [hroots]
      simp
    simpa using hd1

  have h5 : (a - 1) * (a - 3) * (a + 2) * (a + 4) = 0 := by
    nlinarith

  have h6 : (b - 1) * (b - 3) * (b + 2) * (b + 4) = 0 := by
    nlinarith

  have h7 : (c - 1) * (c - 3) * (c + 2) * (c + 4) = 0 := by
    nlinarith

  have h8 : (d - 1) * (d - 3) * (d + 2) * (d + 4) = 0 := by
    nlinarith

  have ha2 : a = 1 ∨ a = 3 ∨ a = -2 ∨ a = -4 := by
    have h9 : (a - 1) * (a - 3) * (a + 2) * (a + 4) = 0 := h5
    cases' (mul_eq_zero.mp h9) with h9a h9b
    · cases' (mul_eq_zero.mp h9a) with h9a1 h9a2
      · cases' (mul_eq_zero.mp h9a1) with h9a1a h9a1b
        · left
          linarith
        · right
          left
          linarith
      · right
        right
        left
        linarith
    · right
      right
      right
      linarith

  have hb2 : b = 1 ∨ b = 3 ∨ b = -2 ∨ b = -4 := by
    have h9 : (b - 1) * (b - 3) * (b + 2) * (b + 4) = 0 := h6
    cases' (mul_eq_zero.mp h9) with h9a h9b
    · cases' (mul_eq_zero.mp h9a) with h9a1 h9a2
      · cases' (mul_eq_zero.mp h9a1) with h9a1a h9a1b
        · left
          linarith
        · right
          left
          linarith
      · right
        right
        left
        linarith
    · right
      right
      right
      linarith

  have hc2 : c = 1 ∨ c = 3 ∨ c = -2 ∨ c = -4 := by
    have h9 : (c - 1) * (c - 3) * (c + 2) * (c + 4) = 0 := h7
    cases' (mul_eq_zero.mp h9) with h9a h9b
    · cases' (mul_eq_zero.mp h9a) with h9a1 h9a2
      · cases' (mul_eq_zero.mp h9a1) with h9a1a h9a1b
        · left
          linarith
        · right
          left
          linarith
      · right
        right
        left
        linarith
    · right
      right
      right
      linarith

  have hd2 : d = 1 ∨ d = 3 ∨ d = -2 ∨ d = -4 := by
    have h9 : (d - 1) * (d - 3) * (d + 2) * (d + 4) = 0 := h8
    cases' (mul_eq_zero.mp h9) with h9a h9b
    · cases' (mul_eq_zero.mp h9a) with h9a1 h9a2
      · cases' (mul_eq_zero.mp h9a1) with h9a1a h9a1b
        · left
          linarith
        · right
          left
          linarith
      · right
        right
        left
        linarith
    · right
      right
      right
      linarith

  rcases ha2 with ha2 | ha2 | ha2 | ha2 <;> rcases hb2 with hb2 | hb2 | hb2 | hb2 <;> rcases hc2 with hc2 | hc2 | hc2 | hc2 <;> rcases hd2 with hd2 | hd2 | hd2 | hd2 <;> 
    norm_num [ha2, hb2, hc2, hd2] at *
    <;> try { 
      tauto 
    }