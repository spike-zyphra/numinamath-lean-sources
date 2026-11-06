import Mathlib

theorem calculus_67478 (h : ∃ t, t > 0 ∧ (14 / 30) * t = 10) :
    t - 14 / 30 = 0.78 := by
  rcases h with ⟨t, ht_pos, ht⟩
  -- ht gives (14 / 30) * t = 10.
  -- But 14 / 30 as natural number division is 0.
  have h1 : (14 / 30) * t = 0 := by
    norm_num
    all_goals omega
  -- But we have from h, (14 / 30) * t = 10
  have h2 : (14 / 30) * t = 10 := ht
  -- Now by transitivity from h1 and h2: 0 = 10
  have h3 : (0 : ℕ) = 10 := by 
    omega
  all_goals 
    omega