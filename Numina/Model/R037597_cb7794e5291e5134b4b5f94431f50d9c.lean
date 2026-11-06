import Mathlib

theorem number_theory_605304 (a b : ℤ) (ha : 0 < a) (hb : 0 < b):
    a^2 + b ∣ a^2 * b + a ∧ b^2 - a ∣ a * b^2 + b ↔
    (a, b) = (a, a + 1) := by 
  constructor 
  · -- Assume the divisibility conditions, prove (a,b) = (a,a+1)
    rintro ⟨h1, h2⟩ 
    have h3 : a ^ 2 + b ∣ a - b ^ 2 := by 
      have h4 : a ^ 2 + b ∣ a ^ 2 * b + a := h1 
      have h5 : a ^ 2 + b ∣ b * (a ^ 2 + b) := by 
        apply dvd_mul_of_dvd_right 
        exact dvd_refl (a ^ 2 + b) 
      have h6 : a ^ 2 + b ∣ (a ^ 2 * b + a - b * (a ^ 2 + b)) := by 
        apply Dvd.dvd.sub 
        · exact h4 
        · exact h5 
      have eq : a ^ 2 * b + a - b * (a ^ 2 + b) = a - b ^ 2 := by 
        ring 
      rw [eq] at h6 
      exact h6 
    have h4 : b ^ 2 - a ∣ a ^ 2 + b := by 
      have h5 : b ^ 2 - a ∣ a * b ^ 2 + b := h2 
      have h6 : b ^ 2 - a ∣ a * (b ^ 2 - a) := by 
        apply dvd_mul_of_dvd_right 
        exact dvd_refl (b ^ 2 - a) 
      have h7 : b ^ 2 - a ∣ (a * b ^ 2 + b - a * (b ^ 2 - a)) := by 
        apply Dvd.dvd.sub 
        · exact h5 
        · exact h6 
      have eq : a * b ^ 2 + b - a * (b ^ 2 - a) = a ^ 2 + b := by 
        ring 
      rw [eq] at h7 
      exact h7 
    obtain ⟨k, hk⟩ := h3 
    obtain ⟨l, hl⟩ := h4 
    have hk1 : a - b ^ 2 = k * (a ^ 2 + b) := by 
      linarith 
    have hl1 : a ^ 2 + b = l * (b ^ 2 - a) := by 
      linarith 
    have h5 : l * k = -1 := by 
      have eq1 : a ^ 2 + b = l * (b ^ 2 - a) := by 
        linarith 
      have eq2 : b ^ 2 - a = - (a - b ^ 2) := by 
        ring 
      rw [show b ^ 2 - a = - (a - b ^ 2) by ring] at eq1 
      rw [show a - b ^ 2 = k * (a ^ 2 + b) by linarith] at eq1 
      have : (a ^ 2 + b) * (1 + l * k) = 0 := by
        nlinarith 
      cases' (mul_eq_zero.mp this) with h6 h7 
      · -- case a^2 + b = 0
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb] 
      · -- case 1 + l * k = 0 
        linarith 
    have h6 : k * l = -1 := by 
      nlinarith 
    have hk2 : k = 1 ∨ k = -1 := by 
      have h7 : k * l = -1 := h6 
      have h8 : k ∣ -1 := by 
        use l 
        all_goals nlinarith 
      have h9 : k ∣ 1 := by
        exact Int.dvd_neg.mp h8 
      have : k = 1 ∨ k = -1 := by 
        have h10 : k ∣ 1 := h9 
        have h11 : k ≤ 1 := by 
          exact Int.le_of_dvd (by norm_num) h10 
        have h12 : k ≥ -1 := by 
          have h13 : -k ∣ 1 := by 
            exact Int.neg_dvd.2 h10 
          have h14 : -k ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h13 
          omega 
        interval_cases k <;> try { tauto } 
      assumption 
    cases' hk2 with hk3 hk4 
    · -- k = 1 
      have h7 : l = -1 := by 
        rw [hk3] at h6 
        nlinarith 
      have hk4 : a - b ^ 2 = a ^ 2 + b := by 
        rw [hk3] at hk1 
        linarith 
      have h77 : b * (b + 1) = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb] 
      cases' (mul_eq_zero.mp h77) with h66 h55 
      · -- b = 0 
        nlinarith 
      · -- b + 1 = 0 
        nlinarith 
    · -- k = -1 
      have h7 : l = 1 := by 
        rw [hk4] at h6 
        nlinarith 
      have hk44 : a - b ^ 2 = - (a ^ 2 + b) := by 
        rw [hk4] at hk1 
        linarith 
      have : (a + b) * (a - b + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp this) with h111 h444 
      · -- a + b = 0 
        nlinarith 
      · -- a - b + 1 = 0 
        have : b = a + 1 := by 
          linarith 
        simp [this] 
  · -- Backward 
    rintro h 
    simp [Prod.ext_iff] at h 
    rcases h with ⟨rfl, h8⟩ 
    constructor 
    · -- Show $a^2 + (a + 1)$ divides $a^2 \cdot (a + 1) + a$
      use a 
      ring 
    · -- Show $(a + 1)^2 - a$ divides $a \cdot (a + 1)^2 + (a + 1)$ 
      use a + 1 
      ring