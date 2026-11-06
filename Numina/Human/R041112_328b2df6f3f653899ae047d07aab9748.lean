import Mathlib


theorem number_theory_272814 {a b c : ℕ} 
    (h : 
        Nat.gcd a b * Nat.lcm b c = Nat.gcd b c * Nat.lcm c a * Nat.gcd c a * Nat.lcm a b ∨
        Nat.gcd b c * Nat.lcm c a = Nat.gcd c a * Nat.lcm a b * Nat.gcd a b * Nat.lcm b c ∨ 
        Nat.gcd c a * Nat.lcm a b = Nat.gcd a b * Nat.lcm b c * Nat.gcd b c * Nat.lcm c a
    ) : (a ∣ b ∨ a ∣ c) ∨ (b ∣ c ∨ b ∣ a) ∨ (c ∣ a ∨ c ∣ b) := by
  -- notice that the conditions are cyclic of a b c, so we can prove for one case and reuse the proof for other cases.
  have h₁: 
      ∀a b c, Nat.gcd a b * Nat.lcm b c = Nat.gcd b c * Nat.lcm c a * Nat.gcd c a * Nat.lcm a b
      →  a ∣ b ∨ (a ∣ c) := by
    intro a b c h'
    by_cases  h_ab: a = 0
    -- apparently a is not zero
    · rw [h_ab] at h'
      simp at h'
      rcases h' with h | h
      · subst a b;
        simp
      · subst a; simp
        by_cases h_b: b = 0
        · left; exact h_b
        · have h_lcm := Nat.lcm_ne_zero (m := b) (n := c) h_b
          rw [not_imp_not] at h_lcm
          have h_lcm := h_lcm h
          right; exact h_lcm               
    · rw [mul_assoc (a := b.gcd c), mul_comm (a := c.lcm a)] at h'
      rw [Nat.gcd_mul_lcm] at h'
      -- next it suffices to analysis case whether lcm a b and lcm b c are zeros
      by_cases h_lcm_ab: lcm a b = 0
      · simp at h_lcm_ab
        cases h_lcm_ab; tauto; subst b; simp
      · by_cases h_lcm_bc: lcm b c = 0
        simp at h_lcm_bc
        cases h_lcm_bc; tauto; subst c; simp
        -- next multiple both side with lcm a b
        have hb: b ≠ 0 := by intro H; subst b; simp at h_lcm_bc
        have h'': (a.lcm b) * (a.gcd b * b.lcm c) = (a.lcm b) * (b.gcd c * (c * a) * a.lcm b) := by
          rw [mul_eq_mul_left_iff]; left; exact h'
        rw [<-mul_assoc, <-mul_comm (a := a.gcd b), Nat.gcd_mul_lcm] at h''
        have h₃: (b.lcm c) * (a * b * b.lcm c) = (b.lcm c) * (a.lcm b * (b.gcd c * (c * a) * a.lcm b)) := by
          rw [mul_eq_mul_left_iff]; left; exact h''
        have h₄: (b.lcm c)^2 * a * b = (b.lcm c * b.gcd c) * (a.lcm b)^2 * c * a := by
          linarith
        rw [mul_comm (b.lcm c), Nat.gcd_mul_lcm] at h₄
        have h₅: b.lcm c ^ 2 = c^2 * a.lcm b ^ 2 := by
          have h_aux: b * c * a.lcm b ^ 2 * c * a = a * b * (a.lcm b ^ 2 * c^2) := by ring
          rw [mul_assoc, mul_comm, h_aux] at h₄
          simp at h₄
          rcases h₄ with h₄ | h₄ | h₄
          · rw [h₄]; linarith
          · exfalso; apply h_ab h₄
          · exfalso; apply hb h₄
        symm at h₅
        have h₆: c * (a.lcm b) = b.lcm c := by
          have h_aux: (c * a.lcm b) ^ 2 = b.lcm c ^ 2 := by linarith
          simp at h_aux; exact h_aux
        
        have h₇: c * a.lcm b * (b.gcd c)= b.lcm c * (b.gcd c) := by
          simp; left; exact h₆
        rw [mul_comm (a := b.lcm c), Nat.gcd_mul_lcm, mul_assoc, mul_comm (b := c)] at h₇
        simp at h₇
        rcases h₇ with h₇ | h₇
        · have ha_dvd := dvd_lcm_left a b
          have h_lcm_dvd: (a.lcm b) ∣ b := by
            conv => rhs; rw [←h₇]
            simp
          left;
          apply dvd_trans ha_dvd h_lcm_dvd
        · subst c; simp
  -- finally we can apply h₁ to the original hypothesis
  rcases h with h | h | h
  · left; apply h₁ a b c h
  · right; left; apply h₁ b c a h
  · right; right; apply h₁ c a b h
    