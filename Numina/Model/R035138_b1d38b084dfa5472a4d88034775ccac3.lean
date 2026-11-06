import Mathlib

theorem algebra_288328 : 
  {b : ℝ | ∃ x y : ℝ, x ≠ y ∧ x^2 - b * x + 12 = 0 ∧ y^2 - b * y + 12 = 0 ∧ x^2 - y^2 = 7} = {7, -7} := by 
  ext b 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor 
  · -- First assume that b is in the set.
    rintro h
    rcases h with ⟨x, y, hxy, hx, hy, hsq⟩
    have h1 : x + y = b := by
      have h2 : (x - y) * (x + y - b) = 0 := by
        nlinarith 
      rcases (mul_eq_zero.mp h2) with (h2 | h3)
      · -- Case x - y = 0, but x ≠ y, contradiction
        exfalso 
        apply hxy 
        linarith 
      · -- Case x + y - b = 0 
        linarith 
    -- Find $xy = 12$ using the equations.
    have h5 : x * y = 12 := by 
      nlinarith [sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by 
        by_contra h'
        have : x = y := by linarith 
        contradiction 
      ), sq_nonneg (x - y)]
    have h3 : (x - y) * b = 7 := by 
      have h5 : (x - y) * (x + y) = 7 := by 
        nlinarith 
      rw [show x + y = b by linarith [h1]] at h5 
      linarith 
    have h6 : (x - y) ^ 2 = b ^ 2 - 48 := by
      have h7 : (x - y) ^ 2 = (x + y) ^ 2 - 4 * (x * y) := by 
        nlinarith 
      rw [show x + y = b by linarith [h1], h5] at h7 
      linarith 
    have h3' : x - y = 7 / b := by 
      have h7 : b ≠ 0 := by 
        by_contra h 
        rw [h] at h3 
        nlinarith 
      field_simp at h3 ⊢ 
      nlinarith 
    have h7 : b ^ 4 - 48 * b ^ 2 - 49 = 0 := by
      have h8 : (x - y) ^ 2 = 49 / b ^ 2 := by
        rw [h3']
        field_simp 
        <;> nlinarith 
      nlinarith [h6, h8]
    have h8 : (b ^ 2 - 49) * (b ^ 2 + 1) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h8) with h9 h10
    · -- Case b² - 49 = 0 
      have h11 : b ^ 2 = 49 := by
        linarith
      have h12 : b = 7 ∨ b = -7 := by 
        have h13 : b ^ 2 = 49 := h11 
        have : b = 7 ∨ b = -7 := by 
          have h14 : b ^ 2 = 49 := h13 
          have : b = 7 ∨ b = -7 := by
            apply eq_or_eq_neg_of_sq_eq_sq 
            norm_num 
            linarith 
          assumption 
        assumption 
      tauto 
    · -- Case b² + 1 = 0 
      have h11 : b ^ 2 = -1 := by 
        nlinarith 
      nlinarith [sq_nonneg b]
  · -- Prove the reverse. 
    rintro (rfl | rfl)
    · -- Case b = 7, use x = 4, y = 3.
      use 4, 3 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num
    · -- Case b = -7, use x = -4, y = -3.
      use -4, -3 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      constructor 
      · norm_num 
      · norm_num