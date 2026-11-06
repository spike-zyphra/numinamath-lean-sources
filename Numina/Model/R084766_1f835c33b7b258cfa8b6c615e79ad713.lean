import Mathlib

theorem number_theory_322120 (a b : ℕ → ℕ) (ha : ∀ n, a n ≤ a (n + 1))
    (hb : ∀ n, b n ≤ b (n + 1)) (h : a 0 ≠ b 0) (h1 : ∀ n, a (n + 2) = a n + a (n + 1))
    (h2 : ∀ n, b (n + 2) = b n + b (n + 1)) (h3 : a 6 = N) (h4 : b 6 = N) :
    N ≥ 104 := by

  have ha1 : a 0 ≤ a 1 := ha 0
  have ha2 : a 1 ≤ a 2 := ha 1
  have ha3 : a 2 ≤ a 3 := ha 2
  have ha4 : a 3 ≤ a 4 := ha 3
  have ha5 : a 4 ≤ a 5 := ha 4
  have ha6 : a 5 ≤ a 6 := ha 5

  have hb1 : b 0 ≤ b 1 := hb 0
  have hb2 : b 1 ≤ b 2 := hb 1
  have hb3 : b 2 ≤ b 3 := hb 2
  have hb4 : b 3 ≤ b 4 := hb 3
  have hb5 : b 4 ≤ b 5 := hb 4
  have hb6 : b 5 ≤ b 6 := hb 5

  have ha2' : a 2 = a 0 + a 1 := h1 0
  have ha3' : a 3 = a 1 + a 2 := by
    specialize h1 1
    simpa using h1
  have ha4' : a 4 = a 2 + a 3 := by
    specialize h1 2
    simpa using h1
  have ha5' : a 5 = a 3 + a 4 := by
    specialize h1 3
    simpa using h1
  have ha6' : a 6 = a 4 + a 5 := by
    specialize h1 4
    simpa using h1

  have hb2' : b 2 = b 0 + b 1 := h2 0
  have hb3' : b 3 = b 1 + b 2 := by
    specialize h2 1
    simpa using h2
  have hb4' : b 4 = b 2 + b 3 := by
    specialize h2 2
    simpa using h2
  have hb5' : b 5 = b 3 + b 4 := by
    specialize h2 3
    simpa using h2
  have hb6' : b 6 = b 4 + b 5 := by
    specialize h2 4
    simpa using h2

  have eq_a4 : a 4 = 2 * a 0 + 3 * a 1 := by
    rw [ha4', ha2', ha3']
    all_goals omega

  have eq_a3 : a 3 = a 0 + 2 * a 1 := by
    rw [ha3', ha2']
    all_goals omega

  have eq_a5 : a 5 = 3 * a 0 + 5 * a 1 := by
    rw [ha5', eq_a3, eq_a4]
    all_goals omega

  have eq_a6 : a 6 = 5 * a 0 + 8 * a 1 := by
    rw [ha6', eq_a4, eq_a5]
    all_goals omega

  have eq_b4 : b 4 = 2 * b 0 + 3 * b 1 := by
    rw [hb4', hb2', hb3']
    all_goals omega

  have eq_b3 : b 3 = b 0 + 2 * b 1 := by
    rw [hb3', hb2']
    all_goals omega

  have eq_b5 : b 5 = 3 * b 0 + 5 * b 1 := by
    rw [hb5', eq_b3, eq_b4]
    all_goals omega

  have eq_b6 : b 6 = 5 * b 0 + 8 * b 1 := by
    rw [hb6', eq_b4, eq_b5]
    all_goals omega

  rw [eq_a6] at h3
  rw [eq_b6] at h4

  have h5 : a 0 ≤ a 1 := ha1
  have h6 : b 0 ≤ b 1 := hb1
  omega