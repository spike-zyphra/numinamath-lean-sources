import Mathlib

open Int

lemma Int.dvd_iff {a b m : ℤ} (h : a ≡ b [ZMOD m]) (hdm : d ∣ m) : d ∣ a ↔ d ∣ b := by
  simp only [← Int.modEq_zero_iff_dvd]
  replace h := h.of_dvd hdm
  exact ⟨h.symm.trans, h.trans⟩

theorem number_theory_4656 {a b c : ℤ} (_ : 0 < c) : a ≡ b [ZMOD c] → a.gcd c = b.gcd c := by
  intro h
  have h1 : a % c = b % c := by 
    exact h
  have eq1 : (a.gcd c : ℤ) = (b.gcd c : ℤ) := by 
    have h4 : (a.gcd c : ℤ) ∣ (b.gcd c : ℤ) := by 
      have h5 : (a.gcd c : ℤ) ∣ (b : ℤ) := by 
        have h6 : (a.gcd c : ℤ) ∣ a := by 
          exact Int.gcd_dvd_left
        have h7 : (a.gcd c : ℤ) ∣ c := by 
          exact Int.gcd_dvd_right 
        -- c divides a - b, so a.gcd c divides a - b
        have h8 : (c : ℤ) ∣ (a - b) := by 
          have h19 : a % c = b % c := h1
          have h20 : (a - b) % c = 0 := by 
            simp [Int.sub_emod, h19]
          exact Int.dvd_of_emod_eq_zero h20 
        have h9 : (a.gcd c : ℤ) ∣ (a - b) := by 
          have h33 : (a.gcd c : ℤ) ∣ c := by 
            exact Int.gcd_dvd_right 
          exact dvd_trans h33 h8 
        -- gcd(a, c) divides a and a-b, so it divides b
        have h10 : (a.gcd c : ℤ) ∣ (b : ℤ) := by
          have h11 : (a.gcd c : ℤ) ∣ a := h6 
          have h12 : (a.gcd c : ℤ) ∣ (a - b) := h9 
          have h13 : (a.gcd c : ℤ) ∣ (a - (a - b) : ℤ) := by 
            apply Dvd.dvd.sub 
            · exact h11 
            · exact h12 
          have h14 : a - (a - b) = b := by omega 
          rw [h14] at h13 
          assumption 
        assumption 
      -- Therefore since a.gcd c divides a and c, it divides b.
      have h6 : (a.gcd c : ℤ) ∣ (b.gcd c : ℤ) := by 
        apply Int.dvd_gcd 
        · exact h5 
        · exact Int.gcd_dvd_right 
      assumption 
    -- Show the reciprocal: b.gcd c divides a.gcd c
    have h7 : (b.gcd c : ℤ) ∣ (a.gcd c : ℤ) := by 
      have h8 : (b.gcd c : ℤ) ∣ (a : ℤ) := by 
        -- We know b.gcd c ∣ b and b.gcd c ∣ c
        have h9 : (b.gcd c : ℤ) ∣ (b : ℤ) := by 
          exact Int.gcd_dvd_left 
        have h10 : (b.gcd c : ℤ) ∣ (c : ℤ) := by 
          exact Int.gcd_dvd_right 
        -- c divides a - b, so b.gcd c divides a - b
        have h11 : (c : ℤ) ∣ (a - b) := by 
          have h19 : a % c = b % c := h1
          have h20 : (a - b) % c = 0 := by 
            simp [Int.sub_emod, h19]
          exact Int.dvd_of_emod_eq_zero h20 
        have h12 : (b.gcd c : ℤ) ∣ (a - b) := by 
          have h33 : (b.gcd c : ℤ) ∣ (c : ℤ) := by 
            exact Int.gcd_dvd_right 
          exact dvd_trans h33 h11 
        -- gcd(b, c) divides b and a-b, so it divides a
        have h13 : (b.gcd c : ℤ) ∣ (a : ℤ) := by 
          have h14 : (b.gcd c : ℤ) ∣ (b : ℤ) := h9 
          have h15 : (b.gcd c : ℤ) ∣ (a - b) := h12 
          have h16 : (b.gcd c : ℤ) ∣ ((a - b) + (b : ℤ)) := by 
            apply Dvd.dvd.add 
            · exact h12 
            · exact h9 
          have h17 : (a - b) + (b : ℤ) = (a : ℤ) := by omega 
          rw [h17] at h16 
          assumption 
        assumption 
      have h8 : (b.gcd c : ℤ) ∣ (a.gcd c : ℤ) := by 
        apply Int.dvd_gcd 
        · exact h8 
        · exact Int.gcd_dvd_right 
      assumption 
    -- Since gcd(a, c) divides gcd(b, c) and gcd(b, c) divides gcd(a, c), they are equal.
    apply Int.dvd_antisymm 
    all_goals
    try { 
      omega 
    }
    all_goals 
    try { 
      tauto 
    }
  exact_mod_cast eq1