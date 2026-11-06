import Mathlib


theorem number_theory_98069 (x y : ℕ) (h1 : IsGreatest {n | ∃ x y z, n = x + y + z ∧ 5*x+10*y+25*z=35} x) (h2 : IsLeast {n | ∃ x y z, n = x + y + z ∧ 5*x+10*y+25*z=35} y) : x - y = 5 := by

  have h3 : x ∈ {n | ∃ x y z, n = x + y + z ∧ 5*x+10*y+25*z=35} := by
    exact h1.left

  have h4 : y ∈ {n | ∃ x y z, n = x + y + z ∧ 5*x+10*y+25*z=35} := by
    exact h2.left

  have h5 : y ≥ 2 := by
    rcases h4 with ⟨d, e, f, h_eq3, h_eq4⟩
    by_contra h
    push_neg at h
    have h6 : y < 2 := by 
      omega
    have h7 : d + e + f < 2 := by 
      omega
    have h8 : d ≤ 1 := by 
      omega
    have h9 : e ≤ 1 := by 
      omega
    have h10 : f ≤ 1 := by 
      omega
    interval_cases d <;> interval_cases e <;> interval_cases f <;> omega

  have h9 : y ≤ 2 := by
    have h8 : 2 ∈ {n | ∃ x y z, n = x + y + z ∧ 5*x+10*y+25*z=35} := by
      use 0, 1, 1
      all_goals norm_num
    have h9 : y ≤ 2 := by
      apply h2.2
      exact h8
    linarith

  have hy : y = 2 := by
    omega

  have hx1 : x ≤ 7 := by
    rcases h3 with ⟨a, b, c, h_eq1, h_eq2⟩
    omega

  have hx2 : x ≥ 7 := by
    have h8 : 7 ∈ {n | ∃ x y z, n = x + y + z ∧ 5*x+10*y+25*z=35} := by
      use 7, 0, 0
      all_goals norm_num
    have hx2 : x ≥ 7 := by
      apply h1.2
      exact h8
    linarith

  have hx : x = 7 := by
    omega

  calc
    x - y = 7 - 2 := by rw [hx, hy]
    _ = 5 := by norm_num