import Mathlib

theorem algebra_258314 :
  { (x, y, z) : ℚ × ℚ × ℚ |
      (∃ r , r ≠ 0 ∧ y = x * r ∧ z = y * r) ∧
      (∃ d , d ≠ 0 ∧ y = x + d ∧ z - 16 = y + d) ∧
      (∃ s , s ≠ 0 ∧ y - 2 = x * s ∧ z - 16 = (y - 2) * s)
  } = { (1, 5, 25), (1/9, 13/9, 169/9) } := by
  ext ⟨x, y, z⟩
  simp [-one_div]
  constructor
  · -- First direction: if (x,y,z) satisfies all three conditions, then (x,y,z) ∈ {(1,5,25), (1/9,13/9,169/9)}.
    rintro ⟨⟨r, hr₀, h₁, h₂⟩, ⟨d, hd₀, h₃, h₄⟩, ⟨s, hs₀, h₅, h₆⟩⟩
    have eq1 : y ^ 2 = x * z := by
      have h3 : y = x * r := h₁
      have h4 : z = y * r := h₂
      calc
        y ^ 2 = (x * r) ^ 2 := by rw [show y = x * r by linarith]
        _ = x ^ 2 * r ^ 2 := by ring
        _ = x * (x * r ^ 2) := by ring
        _ = x * (y * r) := by
          have h5 : x * r ^ 2 = y * r := by
            have h6 : y = x * r := h₁
            rw [show y = x * r by linarith]
            nlinarith
          rw [h5]
        _ = x * z := by
          have h7 : y * r = z := by linarith [h₂]
          rw [h7]
    have eq2 : x + z = 2 * y + 16 := by
      have h7 : y = x + d := by
        linarith [h₃]
      have h8 : z - 16 = y + d := by
        linarith [h₄]
      nlinarith
    have eq3 : (y - 2) ^ 2 = x * (z - 16) := by
      have h6' : y - 2 = x * s := by
        linarith [h₅]
      have h7' : z - 16 = (y - 2) * s := by
        linarith [h₆]
      calc
        (y - 2) ^ 2 = (y - 2) * (y - 2) := by ring
        _ = (y - 2) * (x * s) := by
          rw [show y - 2 = x * s by linarith [h₅]]
        _ = x * ((y - 2) * s) := by ring
        _ = x * (z - 16) := by
          rw [show (y - 2) * s = z - 16 by linarith [h₆]]
    have eq4 : (x - 1) * (x - 1/9) = 0 := by
      nlinarith [sq_pos_of_ne_zero hr₀, sq_pos_of_ne_zero hs₀, sq_pos_of_ne_zero hd₀]
    cases' (mul_eq_zero.mp eq4) with h h
    · -- Case x = 1
      have hx1 : x = 1 := by linarith
      have hy1 : y = 5 := by
        rw [show x = 1 by linarith [hx1]] at eq1 eq2 eq3
        nlinarith
      have h2 : z = 25 := by
        rw [show x = 1 by linarith, show y = 5 by linarith] at eq1
        nlinarith
      simp [hx1, hy1, h2]
    · -- Case x = 1/9
      have hx2 : x = 1/9 := by linarith
      have h1 : y = 13/9 := by
        rw [show x = 1/9 by linarith [hx2]] at eq1 eq2 eq3
        nlinarith
      have h2 : z = 169/9 := by
        rw [show y = 13/9 by linarith, show x = 1/9 by linarith] at eq1
        nlinarith
      simp [hx2, h1, h2]
  · -- Second direction: if (x,y,z) ∈ {(1,5,25), (1/9,13/9,169/9)}, then (x,y,z) satisfies all three conditions.
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · constructor
      · use 5
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      constructor
      · use 4
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · use 3
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
    · constructor
      · use 13
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      constructor
      · use 4/3
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · use -5
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num