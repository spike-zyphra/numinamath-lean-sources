import Mathlib

theorem  number_theory_626484 {n : ℤ}
  (hn : ∃ x y : ℤ, x ≠ y ∧ x^2 - 6*x - 4*n^2 - 32*n = 0
                         ∧ y^2 - 6*y - 4*n^2 - 32*n = 0)
  : n ∈ ({10, 0, -18, -8} : Set _):=
by
  rcases hn with ⟨x, y, hxy, hx, hy⟩
  have h1 : (x - y) * (x + y - 6) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h1) with
  | inl h2 =>
    have h3 : x = y := by linarith
    exfalso; exact hxy (by linarith)
  | inr h2 =>
    have h4 : x + y = 6 := by linarith
    have h3 : ∃ k : ℤ, (4 * n^2 + 32 * n + 9 : ℤ) = k^2 := by
      use x - 3
      nlinarith
    rcases h3 with ⟨k, hk⟩
    have h7 : (2 * n + 8 - k) * (2 * n + 8 + k) = 55 := by
      nlinarith
    have h8 : (2 * n + 8 - k) ∣ 55 := by
      use (2 * n + 8 + k)
      all_goals linarith
    have h10 : n = 10 ∨ n = 0 ∨ n = -18 ∨ n = -8 := by
      have h13 : (2 * n + 8 - k) ∣ 55 := h8
      have h14 : (2 * n + 8 - k) ≤ 55 := by
        exact Int.le_of_dvd (by norm_num) h13
      have h15 : (2 * n + 8 - k) ≥ -55 := by
        have h16 : -(2 * n + 8 - k) ∣ 55 := by
          exact Int.neg_dvd.2 h13
        have h17 : -(2 * n + 8 - k) ≤ 55 := by
          exact Int.le_of_dvd (by norm_num) h16
        omega
      interval_cases h18 : (2 * n + 8 - k) <;> omega
    simp at h10 ⊢
    tauto