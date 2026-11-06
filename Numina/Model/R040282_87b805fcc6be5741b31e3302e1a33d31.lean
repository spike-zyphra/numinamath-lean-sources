import Mathlib

theorem algebra_269719 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c = 44 ∧ a * c + b * c = 23}.ncard = 2 := by 
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b + b * c = 44 ∧ a * c + b * c = 23} = {(21, 2, 1), (1, 22, 1)} := by 
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- Assume ⟨a, b, c⟩ satisfies the conditions
      rintro ⟨ha, hb, hc, h1, h2⟩

      have h3 : c = 1 ∨ c = 23 := by
        have h4 : c ∣ 23 := by
          use (a + b)
          linarith
        have h5 : c ∣ 23 := h4
        have h6 : c ≤ 23 := by
          exact Nat.le_of_dvd (by norm_num) h5
        interval_cases c <;> try { tauto }
        all_goals omega

      rcases h3 with (hc1 | hc23)
      · -- c = 1
        have h4 : a + b = 23 := by
          rw [hc1] at h2
          nlinarith
        have h4' : b * (a + 1) = 44 := by
          rw [hc1] at h1
          linarith
        have h4'' : b ≤ 44 := by 
          by_contra h
          push_neg at h
          have h7 : b * (a + 1) = 44 := h4'
          have h8 : b > 44 := by linarith
          have h9 : a + 1 > 0 := by nlinarith
          have h10 : b * (a + 1) > 44 := by 
            nlinarith [show a + 1 ≥ 1 by omega]
          linarith
        interval_cases b <;> omega
      · -- c = 23
        have h4 : a + b = 1 := by
          rw [hc23] at h2
          nlinarith
        omega
    · -- Show that (21, 2, 1) and (1, 22, 1) satisfy the conditions.
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- Check (21, 2, 1)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check (1, 22, 1)
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair (by norm_num)]
  all_goals try { native_decide }
  all_goals try { linarith }
  all_goals try { native_decide }
  all_goals try { linarith }