import Mathlib

theorem algebra_241828 (a d : ℚ) (h₀ : 0 < d) (h₁ : ∃ n : ℕ, a + a + d + a + 2 * d + a + 3 * d = n)
    (h₂ : ∃ m : ℕ, a + a + d + a + 2 * d + a + 3 * d + a + 4 * d + a + 5 * d + a + 6 * d = m)
    (h₃ : a ≤ 2 / 3) :
    a ≤ 9 / 14 := by
  rcases h₁ with ⟨n, hn⟩
  rcases h₂ with ⟨m, hm⟩
  have eq1 : 4 * a + 6 * d = (↑n : ℚ) := by
    linarith
  have eq2 : 7 * a + 21 * d = (↑m : ℚ) := by
    linarith
  have eq3 : a = (7 * (↑n : ℚ) - 2 * (↑m : ℚ)) / 14 := by
    linarith [eq1, eq2]
  have eq4 : (7 * (↑n : ℚ) - 2 * (↑m : ℚ)) / 14 ≤ 2 / 3 := by 
    nlinarith [h₃, eq3]
  have eq5 : 3 * (7 * (↑n : ℚ) - 2 * (↑m : ℚ)) ≤ 28 := by 
    linarith [eq4]
  have eq6 : 3 * (7 * (n : ℤ) - 2 * (m : ℤ)) ≤ 28 := by
    exact_mod_cast eq5
  have eq7 : 7 * (n : ℤ) - 2 * (m : ℤ) ≤ 9 := by
    omega
  have eq8 : (7 * (↑n : ℚ) - 2 * (↑m : ℚ)) ≤ 9 := by 
    exact_mod_cast eq7
  linarith [eq3, eq8]