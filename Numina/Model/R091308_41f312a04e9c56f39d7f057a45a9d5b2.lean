import Mathlib

theorem number_theory_243654 (a : ℕ → ℚ) (ha : ∀ n, a n = (n + 1) / (n + 2)) :
    ∀ i j, i ≠ j → a i ≠ a j := by
  intro i j h_ne
  intro h_eq
  have h_i : a i = (i + 1) / (i + 2) := ha i
  have h_j : a j = (j + 1) / (j + 2) := ha j
  rw [h_i, h_j] at h_eq
  have h1 : ((i : ℚ) + 1) / ((i : ℚ) + 2) = ((j : ℚ) + 1) / ((j : ℚ) + 2) := by
    exact_mod_cast h_eq
  have h2 : ((i : ℚ) + 1) * ((j : ℚ) + 2) = ((j : ℚ) + 1) * ((i : ℚ) + 2) := by
    field_simp [(show (i : ℚ) + 2 ≠ 0 by linarith), (show (j : ℚ) + 2 ≠ 0 by linarith)] at h1 ⊢
    nlinarith
  have h3 : (i : ℚ) * (j : ℚ) + 2 * (i : ℚ) + (j : ℚ) + 2 = (j : ℚ) * (i : ℚ) + 2 * (j : ℚ) + (i : ℚ) + 2 := by
    nlinarith [h2]
  have h4 : 2 * (i : ℚ) + (j : ℚ) = 2 * (j : ℚ) + (i : ℚ) := by
    nlinarith [h3]
  have h5 : (i : ℚ) = (j : ℚ) := by
    nlinarith [h4]
  have h6 : i = j := by
    exact_mod_cast h5
  contradiction