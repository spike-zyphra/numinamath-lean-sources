import Mathlib

theorem number_theory_112441 (x y z : ℕ) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : x / y = 4 ∧ x % y = 3) (h2 : y / z = 5 ∧ y % z = 4)
    (h3 : x + y + z = 153) :
    x = 119 ∧ y = 29 ∧ z = 5 := by
  rcases h1 with ⟨hx1, hx2⟩
  rcases h2 with ⟨hy1, hy2⟩
  have eq1 : x = 4 * y + 3 := by
    rw [←Nat.div_add_mod x y, hx1, hx2]
    all_goals nlinarith
  have eq2 : y = 5 * z + 4 := by
    rw [←Nat.div_add_mod y z, hy1, hy2]
    all_goals nlinarith
  have h4 : z = 5 := by
    rw [eq1, eq2] at h3
    omega
  have h5 : y = 29 := by 
    nlinarith [eq2, h4]
  have h6 : x = 119 := by 
    nlinarith [eq1, h5, h4]
  exact ⟨h6, h5, h4⟩