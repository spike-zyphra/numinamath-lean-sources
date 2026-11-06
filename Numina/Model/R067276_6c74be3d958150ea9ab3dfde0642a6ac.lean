import Mathlib

theorem number_theory_3822 : IsGreatest {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ (1 / x : ℚ) + 1 / y = 1 / 2023} 4094552 := by 
  constructor
  · -- Show 4094552 is in the set
    use 2024
    all_goals norm_num
  · -- Show that for any x in the set, x ≤ 4094552
    intro x hx
    rcases hx with ⟨y, hx_pos, hy_pos, heq⟩
    by_contra h
    push_neg at h
    have h_eq1 : (x : ℚ) > 0 := by exact_mod_cast (show x > 0 by linarith)
    have h_eq2 : (y : ℚ) > 0 := by exact_mod_cast (show y > 0 by linarith)
    have h_eq5 : (x : ℚ) * (y : ℚ) = 2023 * ((x : ℚ) + (y : ℚ)) := by
      have h_eq1 : (x : ℚ) > 0 := by exact_mod_cast (show x > 0 by linarith)
      have h_eq2 : (y : ℚ) > 0 := by exact_mod_cast (show y > 0 by linarith)
      field_simp at heq ⊢
      linarith
    have h_eq6 : x ≤ 4094552 := by
      by_contra h2
      push_neg at h2
      have h2' : x > 2023 := by
        omega
      have h8 : y < x := by
        have h5 : x * y = 2023 * (x + y) := by
          have h_eq1 : (x : ℚ) > 0 := by exact_mod_cast (show x > 0 by linarith)
          have h_eq2 : (y : ℚ) > 0 := by exact_mod_cast (show y > 0 by linarith)
          have h_eq5 : (x : ℚ) * (y : ℚ) = 2023 * ((x : ℚ) + (y : ℚ)) := by 
            have h_eq1 : (x : ℚ) > 0 := by exact_mod_cast (show x > 0 by linarith)
            have h_eq2 : (y : ℚ) > 0 := by exact_mod_cast (show y > 0 by linarith)
            field_simp at heq ⊢
            linarith
          exact_mod_cast h_eq5
        have h9 : (2023 : ℕ) * x < x * y := by
          nlinarith
        have h10 : y > 2023 := by
          nlinarith
        nlinarith
      -- magnification
      have h9 : x * y = 2023 * (x + y) := by
        have h_eq1 : (x : ℚ) > 0 := by exact_mod_cast (show x > 0 by linarith)
        have h_eq2 : (y : ℚ) > 0 := by exact_mod_cast (show y > 0 by linarith)
        have h_eq5 : (x : ℚ) * (y : ℚ) = 2023 * ((x : ℚ) + (y : ℚ)) := by 
          have h_eq1 : (x : ℚ) > 0 := by exact_mod_cast (show x > 0 by linarith)
          have h_eq2 : (y : ℚ) > 0 := by exact_mod_cast (show y > 0 by linarith)
          field_simp at heq ⊢
          linarith
        exact_mod_cast h_eq5
      -- exploration
      have h10 : y < x := by
        have h9 : (2023 : ℕ) * x < x * y := by
          nlinarith
        have h10 : y > 2023 := by
          nlinarith
        nlinarith
      -- producing by grid example n project max candidate re reduce reverse stage
      have h11 : y < 2024 := by
        nlinarith [h9, h2']
      -- generating 
      have h12 : x > 0 := by linarith
      -- creating contradiction due to constraints
      have h13 : y > 0 := by linarith
      -- looking for contradiction with all bounds
      interval_cases y <;> omega
    -- generating side upper towards bound
    omega