import Mathlib

theorem algebra_15311  :
  IsLeast {k | ∃ a b : ℤ, a ≠ b ∧ b ≠ k ∧ a ≠ k ∧ ∀ x, (a*x+ b)*(b*x+a) = 26*x^2+k*x+26 } 173 := by
    constructor
    · -- Show that 173 is in the set.
      use 2, 13
      constructor
      · -- Show a ≠ b
        norm_num
      constructor
      · -- Show b ≠ k
        norm_num
      constructor
      · -- Show a ≠ k
        norm_num
      · -- Show that the polynomial identity holds for all x.
        intro x
        ring_nf
    · -- Show that 173 is minimal.
      intro k hk
      rcases hk with ⟨a, b, hab, hbhk, hak, h⟩ 
      have h1 := h 0
      have h2 := h 1
      have h3 := h (-1)
      -- From x=0: (a * 0 + b) * (b * 0 + a) = b * a = 26
      have h4 : a * b = 26 := by
        linarith
      -- From x=1: (a + b)^2 = 52 + k
      have h5 : (a + b) ^ 2 = 52 + k := by
        nlinarith
      have h7 : k ≥ 173 := by
        have h8 : a * b = 26 := h4
        have h9 : a ∣ 26 := by
          use b
          all_goals nlinarith
        have h10 : a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2 ∨ a = 13 ∨ a = -13 ∨ a = 26 ∨ a = -26 := by
          have h4 : a ∣ 26 := h9
          have h5 : a ≤ 26 := by
            apply Int.le_of_dvd (by norm_num) h4
          have h6 : a ≥ -26 := by
            have h7 : (-a) ∣ 26 := by
              exact Int.neg_dvd.2 h4
            have h8 : -a ≤ 26 := by
              apply Int.le_of_dvd (by norm_num) h7
            omega
          interval_cases a <;> try { tauto }
        rcases h10 with (ha | ha | ha | ha | ha | ha | ha | ha)
        · -- Substitute a = 1
          have hb : b = 26 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = -1
          have hb : b = -26 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = 2
          have hb : b = 13 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = -2
          have hb : b = -13 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = 13
          have hb : b = 2 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = -13
          have hb : b = -2 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = 26
          have hb : b = 1 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
        · -- Substitute a = -26
          have hb : b = -1 := by
            rw [ha] at h4
            nlinarith
          rw [ha, hb] at h5
          nlinarith
      linarith