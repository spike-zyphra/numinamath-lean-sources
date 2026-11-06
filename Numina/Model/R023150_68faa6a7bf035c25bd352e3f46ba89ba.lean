import Mathlib

theorem number_theory_188911 (x : ℤ) (hx : x ≡ 3 [ZMOD 7]) (hxp : x^2 ≡ 44 [ZMOD 7^2])
    (hxp' : x^3 ≡ 111 [ZMOD 7^3]) :
    x ≡ 17 [ZMOD 343] := by
  norm_num [Int.ModEq] at hx hxp hxp' ⊢
  have h1 : x % 7 = 3 := by 
    omega
  have h2 : x % 49 = 17 := by
    have h1' : x % 7 = 3 := h1
    have hx2 : x ^ 2 % 49 = 44 := hxp
    have h3 : x % 49 = 17 := by 
      have h5 : x % 7 = 3 := by 
        omega
      have h6 : x % 49 = 17 := by
        have h7 : x % 7 = 3 := h5
        have h8 : x ^ 2 % 49 = 44 := by
          omega
        have h10 : x % 49 = 3 ∨ x % 49 = 10 ∨ x % 49 = 17 ∨ x % 49 = 24 ∨ x % 49 = 31 ∨ x % 49 = 38 ∨ x % 49 = 45 := by
          omega
        rcases h10 with (h | h | h | h | h | h | h)
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
          <;> tauto 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
        · 
          simp [pow_two, Int.add_emod, Int.mul_emod, h] at h8
          all_goals 
          omega 
        all_goals 
          omega 
      exact h6
    exact h3
  -- Now prove the congruence modulo 343
  have h3 : x % 343 = 17 := by
    -- Given data
    have hx33 : x % 49 = 17 := h2
    have hx1 : x % 7 = 3 := h1
    -- And the hypothesis hxp'
    have hx44 : x ^ 3 % 343 = 111 := hxp'
    have h6 : x % 343 = 17 := by
      -- Now can establish the congruence by exhaustive search.
      have h7 : x % 49 = 17 := by
        omega
      -- Now can establish the congruence by exhaustive search.
      have h9 : x % 343 = 17 ∨ x % 343 = 17 + 49 ∨ x % 343 = 17 + 49*2 ∨ x % 343 = 17 + 49*3 ∨ 
        x % 343 = 17 + 49*4 ∨ x % 343 = 17 + 49*5 ∨ x % 343 = 17 + 49*6 := by 
        omega 
      rcases h9 with (h | h | h | h | h | h | h)
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      · 
        simp [pow_succ, Int.add_emod, Int.mul_emod, h] at hx44 ⊢
        all_goals 
        omega 
      all_goals 
        omega 
    exact h6
  show x % 343 = 17
  omega