import Mathlib

theorem algebra_240449 (a b : ℤ) : a * (a - b) = b ↔ (a, b) = (0, 0) ∨ (a, b) = (-2, -4) := by 
  constructor
  · -- Assume a * (a - b) = b, prove (a, b) = (0, 0) ∨ (a, b) = (-2, -4)
    intro h 
    have eq1 : a * (a - b) = b := h
    have eq2 : a ^ 2 - a * b - b = 0 := by 
      linarith [eq1]
    have eq3 : a ^ 2 = b * (a + 1) := by 
      nlinarith
    -- From a^2 = b * (a + 1), we know that a + 1 divides a^2
    have h1 : a + 1 ∣ a ^ 2 := by 
      use b 
      linarith [eq3]
    have h5 : a + 1 ∣ a ^ 2 := h1
    -- Since a + 1 divides a^2 and gcd(a, a + 1) = 1, then a + 1 divides a
    have h4 : IsCoprime (a + 1) a := by 
      use 1, -1
      all_goals 
        ring
    -- Now since h4 : IsCoprime (a + 1) a and h5 : a + 1 ∣ a ^ 2, which is a * a
    -- We can use the property that if n | k*m and IsCoprime n k, then n | m
    have h6 : a + 1 ∣ a * a := by 
      have h7 : a + 1 ∣ a ^ 2 := h5
      have h8 : a ^ 2 = a * a := by ring 
      rw [h8] at h7
      exact h7
    -- Therefore, a + 1 divides a
    have h8 : a + 1 ∣ a := by 
      have h9 : IsCoprime (a + 1) a := h4
      exact IsCoprime.dvd_of_dvd_mul_left h9 h6 
    -- If a + 1 divides a, then a + 1 divides a
    -- So a + 1 divides a - (a + 1) = -1
    have h10 : a + 1 ∣ 1 := by 
      have h11 : a + 1 ∣ a := h8
      have h12 : a + 1 ∣ (a : ℤ) - (a + 1 : ℤ) := by 
        apply Dvd.dvd.sub (show a + 1 ∣ a by exact h11) (show a + 1 ∣ a + 1 by exact dvd_refl (a + 1))
      have h13 : (a : ℤ) - (a + 1 : ℤ) = -1 := by 
        linarith 
      rw [h13] at h12 
      have h14 : a + 1 ∣ -1 := h12 
      have : a + 1 ∣ 1 := by 
        exact Int.dvd_neg.mpr h14 
      exact this 
    -- Now from a + 1 ∣ 1, we have that a + 1 is either 1 or -1
    have h13 : a + 1 = 1 ∨ a + 1 = -1 := by 
      have h14 : a + 1 ∣ 1 := h10 
      have h15 : a + 1 = 1 ∨ a + 1 = -1 := by 
        have h16 : a + 1 ∣ 1 := h14 
        have h17 : a + 1 ≤ 1 := by 
          apply Int.le_of_dvd (by norm_num) h16 
        have h18 : a + 1 ≥ -1 := by 
          have h19 : -(a + 1) ∣ 1 := by 
            exact Int.neg_dvd.2 h16 
          have h20 : -(a + 1) ≤ 1 := by 
            apply Int.le_of_dvd (by norm_num) h19 
          linarith 
        interval_cases (a + 1) <;> tauto 
      exact h15 
    cases h13 with 
    | inl h14 => 
      -- From a + 1 = 1, we get a = 0 
      have ha : a = 0 := by 
        linarith 
      -- From eq3: a^2 = b * (a + 1)
      -- 0^2 = b * (0 + 1) => 0 = b 
      have hb : b = 0 := by 
        rw [ha] at eq3 
        nlinarith 
      -- So we get the pair (0, 0)
      left 
      simp [Prod.ext_iff, ha, hb] 
    | inr h15 => 
      -- From a + 1 = -1, we get a = -2 
      have ha : a = -2 := by 
        linarith 
      -- From eq3: a^2 = b * (a + 1)
      -- (-2)^2 = b * (-2 + 1) => 4 = b * (-1) => b = -4 
      have hb : b = -4 := by 
        rw [ha] at eq3 
        nlinarith 
      -- So we get the pair (-2, -4)
      right 
      simp [Prod.ext_iff, ha, hb] 
  · -- Assume (a, b) = (0, 0) ∨ (a, b) = (-2, -4), prove a * (a - b) = b
    rintro (h | h)
    · -- Case (a, b) = (0, 0)
      simp [Prod.ext_iff] at h 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals 
        norm_num 
    · -- Case (a, b) = (-2, -4)
      simp [Prod.ext_iff] at h 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals 
        norm_num