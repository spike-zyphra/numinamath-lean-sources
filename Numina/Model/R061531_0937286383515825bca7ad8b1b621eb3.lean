import Mathlib

theorem algebra_182046 {n : ℕ} (hn : n ≥ 2) (a : Fin n → ℝ) (M : ℝ)
    (hM : ∑ i : Fin n, a i = M * n) (hM1 : ∑ i : Fin n, a i + 15 = (M + 2) * (n + 1))
    (hM2 : ∑ i : Fin n, a i + 15 + 1 = (M + 1) * (n + 2)) :
    n = 4 := by
  have eq1 : (M * n : ℝ) + 15 = (M + 2) * (n + 1) := by
    linarith [hM, hM1]

  have eq2 : (M * n : ℝ) + 16 = (M + 1) * (n + 2) := by
    linarith [hM, hM2]

  have eq3 : (2 : ℝ) * (n : ℝ) + M = 13 := by
    have h1 := eq1
    ring_nf at h1 ⊢
    linarith

  have eq4 : (2 : ℝ) * M + (n : ℝ) = 14 := by
    have h1 := eq2
    ring_nf at h1 ⊢
    linarith

  have hn' : (n : ℝ) ≥ (2 : ℝ) := by
    exact_mod_cast hn

  have h1 : (n : ℝ) = 4 := by
    have h_eq3 := eq3
    have h_eq4 := eq4
    linarith [h_eq3, h_eq4]

  have hn4 : n = 4 := by
    exact_mod_cast h1
  exact hn4