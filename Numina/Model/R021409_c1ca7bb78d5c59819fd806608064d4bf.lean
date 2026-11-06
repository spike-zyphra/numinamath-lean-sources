import Mathlib

theorem number_theory_31614 :
    IsGreatest {t : ℕ | ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x < y ∧ y < z ∧ x + x * y + x * y * z = 37 ∧ t = x + y + z} 20 := by
  constructor
  · -- Show 20 is achievable
    use 1, 2, 17
    all_goals norm_num
  · -- Show no greater value is achievable
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, hxy1, hxy2, heq, ht⟩
    have h1 : x ∣ 37 := by
      use 1 + y + y * z
      linarith
    have h2 : x = 1 ∨ x = 37 := by
      have h3 : x ≤ 37 := by
        exact Nat.le_of_dvd (show 0 < 37 by norm_num) h1
      interval_cases x <;> omega
    rcases h2 with hx1 | hx37
    · -- Case x = 1
      have h_eq1 : 1 + y + y * z = 37 := by
        rw [hx1] at heq
        linarith
      have h_eq2 : y * (1 + z) = 36 := by
        nlinarith
      have h3 : y ∣ 36 := by
        use 1 + z
        linarith
      have h4 : y ≤ 36 := by
        exact Nat.le_of_dvd (show 0 < 36 by norm_num) h3
      interval_cases y <;> omega
    · -- Case x = 37
      have h_eq1 : 1 + y + y * z = 1 := by
        rw [hx37] at heq
        linarith
      have h_eq2 : y * (1 + z) = 0 := by
        nlinarith
      have h_eq3 : y > 0 := by linarith
      have h_eq4 : 1 + z > 0 := by linarith
      have h_eq5 : y * (1 + z) > 0 := by
        positivity
      linarith