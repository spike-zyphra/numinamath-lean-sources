import Mathlib

theorem algebra_290597 :
    {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | 
        ∃ x y : ℝ, 
        a = x + 6 ∧ b = x ∧ 
        c = y + 5 ∧ d = y ∧ 
        (x + 6) / x = (y + 5) / y ∧ 
        a^2 + b^2 + c^2 + d^2 = 793} = 
    {(18, 12, 15, 10), (-12, -18, -10, -15)} := by
  ext ⟨a, b, c, d⟩
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.forall]
  constructor
  · -- Forward direction
    rintro ⟨x, y, ha, hb, hc, hd, h1, h2⟩
    have h3 : x ≠ 0 := by
      by_contra h
      rw [show x = (0 : ℝ) by linarith] at h1
      have h30 : (0 + 6) / (0 : ℝ) = 0 := by norm_num
      rw [h30] at h1
      have h11 : (y + 5) / y = 0 := by
        linarith
      have h31 : y = 0 := by
        by_cases h4 : y = 0
        · exact h4
        · 
          have h40 : y ≠ 0 := by
            exact h4
          have h110 : (y + 5) / y = 0 := by
            linarith
          have h7 : y + 5 = 0 := by 
            field_simp at h110 ⊢
            all_goals nlinarith
          nlinarith
      have h30 : a^2 + b^2 + c^2 + d^2 = 793 := h2
      have h12 : a = 6 := by 
        rw [show x = (0 : ℝ) by linarith] at ha
        nlinarith
      have h13 : b = 0 := by
        rw [show x = (0 : ℝ) by linarith] at hb
        nlinarith
      have h14 : c = 5 := by
        rw [show y = (0 : ℝ) by linarith [h31] ] at hc
        nlinarith
      have h15 : d = 0 := by
        rw [show y = (0 : ℝ) by linarith [h31] ] at hd
        nlinarith
      rw [h12, h13, h14, h15] at h30
      norm_num at h30 
    have h4 : y ≠ 0 := by
      by_contra h
      rw [show y = (0 : ℝ) by linarith] at h1
      have h32 : (x + 6) / x = 0 := by 
        rw [h1]
        norm_num [show y = (0 : ℝ) by linarith]
      have h11 : x ≠ 0 := h3
      have h33 : x + 6 = 0 := by
        have h44 : (x + 6) / x = 0 := h32
        field_simp [h3] at h44 ⊢
        all_goals nlinarith
      have h34 : x = -6 := by
        nlinarith
      have h30 : a^2 + b^2 + c^2 + d^2 = 793 := h2
      have h12 : a = 0 := by 
        rw [show x = (-6 : ℝ) by linarith [h34] ] at ha
        nlinarith
      have h13 : b = -6 := by
        rw [show x = (-6 : ℝ) by linarith [h34] ] at hb
        nlinarith
      have h14 : c = 5 := by
        rw [show y = (0 : ℝ) by linarith [show y = (0 : ℝ) by linarith] ] at hc
        nlinarith
      have h15 : d = 0 := by
        rw [show y = (0 : ℝ) by linarith [show y = (0 : ℝ) by linarith] ] at hd
        nlinarith
      rw [h12, h13, h14, h15] at h30
      norm_num at h30 
    have h15 : (x + 6) * y = x * (y + 5) := by
      have h7 : x ≠ 0 := h3
      have h8 : y ≠ 0 := h4
      field_simp at h1 ⊢
      nlinarith
    have h7 : 6 * y = 5 * x := by
      nlinarith
    have h8 : y = (5/6) * x := by
      linarith
    rw [ha, hb, hc, show d = (5/6) * x by nlinarith [h8]] at h2
    have h11 : 61 * x^2 + 366 * x - 13176 = 0 := by
      nlinarith
    have h13 : (x - 12) * (x + 18) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h13) with h14 h15
    · 
      have hx12 : x = 12 := by linarith
      have hy12 : y = 10 := by
        rw [show x = (12 : ℝ) by linarith] at h8
        nlinarith
      have ha18 : a = 18 := by
        rw [show x = (12 : ℝ) by linarith] at ha
        nlinarith
      have hb12 : b = 12 := by
        rw [show x = (12 : ℝ) by linarith] at hb
        nlinarith
      have hc15 : c = 15 := by
        rw [show y = (10 : ℝ) by linarith [h8, hx12]] at hc
        nlinarith
      have h110 : d = 10 := by
        rw [show y = (10 : ℝ) by linarith [h8, hx12] ] at hd
        nlinarith
      left
      simp [ha18, hb12, hc15, h110]
    · 
      have hx18 : x = -18 := by linarith
      have hy15 : y = -15 := by
        rw [show x = (-18 : ℝ) by linarith] at h8
        nlinarith
      have ha12 : a = -12 := by
        rw [show x = (-18 : ℝ) by linarith] at ha
        nlinarith
      have hb18 : b = -18 := by
        rw [show x = (-18 : ℝ) by linarith] at hb
        nlinarith
      have hc10 : c = -10 := by
        rw [show y = (-15 : ℝ) by linarith [h8, hx18] ] at hc
        nlinarith
      have h115 : d = -15 := by
        rw [show y = (-15 : ℝ) by linarith [h8, hx18] ] at hd
        nlinarith
      right
      simp [ha12, hb18, hc10, h115]
  · -- Backward direction
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · 
      use (12 : ℝ), (10 : ℝ)
      norm_num
    · 
      use (-18 : ℝ), (-15 : ℝ)
      norm_num