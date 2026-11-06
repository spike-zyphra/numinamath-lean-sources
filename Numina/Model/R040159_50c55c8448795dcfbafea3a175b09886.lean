import Mathlib

theorem algebra_136515 (x y : ℤ) :
    x^2 + 2 * x * y + 3 * y^2 - 2 * x + y + 1 = 0 ↔
    (x, y) = (1, 0) ∨ (x, y) = (1, -1) ∨ (x, y) = (3, -1) := by
  constructor
  · -- Assume the equation holds, prove the three possible pairs
    rintro h_eq
    have eq1 : (x + y - 1) ^ 2 + 2 * y^2 + 3 * y = 0 := by
      nlinarith
    have h1 : y ≥ -1 := by 
      nlinarith [sq_nonneg (y + 1), sq_nonneg (x + y - 1)]
    have h2 : y ≤ 0 := by 
      nlinarith [sq_nonneg (y + 1), sq_nonneg (x + y - 1)]
    have h3 : y = 0 ∨ y = -1 := by 
      omega
    rcases h3 with (h_y0 | h_y1)
    · -- y = 0
      rw [show y = 0 by linarith] at eq1
      have h_eq0 : (x - 1) ^ 2 = 0 := by
        ring_nf at eq1 
        nlinarith
      have hx : x = 1 := by 
        nlinarith
      left 
      simp [hx, show y = 0 by linarith]
    · -- y = -1
      rw [show y = -1 by linarith] at eq1 
      have h_eq1 : (x - 2) ^ 2 = 1 := by
        nlinarith
      have hx1 : x = 1 ∨ x = 3 := by
        have hx2 : (x - 2) ^ 2 = 1 := h_eq1
        have hx3 : x - 2 = 1 ∨ x - 2 = -1 := by 
          have h : (x - 2) ^ 2 = 1 := hx2
          have : x - 2 = 1 ∨ x - 2 = -1 := by 
            have h1 : (x - 2) ^ 2 - 1 = 0 := by linarith
            have : (x - 2 - 1) * (x - 2 + 1) = 0 := by 
              ring_nf at h1 ⊢
              linarith 
            cases' (mul_eq_zero.mp this) with h2 h3 
            · left
              linarith 
            · right 
              linarith 
          assumption 
        cases' hx3 with h4 h5 
        · -- x - 2 = 1 
          right 
          linarith 
        · -- x - 2 = -1 
          left 
          linarith
      cases hx1 with
      | inl h31 => 
        right 
        left 
        simp [h31, show y = -1 by linarith]
      | inr h31 => 
        right 
        right 
        simp [h31, show y = -1 by linarith]
  · -- Assume the pairs, prove the equation
    rintro (h | h | h)
    · -- First pair (1, 0)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Second pair (1, -1)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Third pair (3, -1)
      simp [Prod.ext_iff] at h
      rcases h with ⟨rfl, rfl⟩
      norm_num