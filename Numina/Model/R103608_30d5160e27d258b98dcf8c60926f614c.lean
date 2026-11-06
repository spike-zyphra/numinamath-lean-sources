import Mathlib

theorem algebra_314558 {a : ℕ → ℤ} (ha : ∀ n, 1 ≤ n ∧ n ≤ 5 → a n = n ^ 2)
    (h : ∀ n, 0 < n → a (n + 5) + a (n + 1) = a (n + 4) + a n) :
    a 2023 = 17 := by
  have ha1 : a 1 = 1 := by
    specialize ha 1 (by norm_num)
    norm_num at ha ⊢
    linarith
  have ha2 : a 2 = 4 := by
    specialize ha 2 (by norm_num)
    norm_num at ha ⊢
    linarith
  have ha3 : a 3 = 9 := by
    specialize ha 3 (by norm_num)
    norm_num at ha ⊢
    linarith
  have ha4 : a 4 = 16 := by
    specialize ha 4 (by norm_num)
    norm_num at ha ⊢
    linarith
  have ha5 : a 5 = 25 := by
    specialize ha 5 (by norm_num)
    norm_num at ha ⊢
    linarith
  have ha6 : a 6 = 22 := by
    have eq1 := h 1 (by norm_num)
    norm_num at eq1
    linarith [ha2, ha5, ha1, eq1]
  have ha7 : a 7 = 17 := by
    have eq1 := h 2 (by norm_num)
    norm_num at eq1
    linarith [ha3, ha6, ha2, eq1]
  have ha8 : a 8 = 10 := by
    have eq1 := h 3 (by norm_num)
    norm_num at eq1
    linarith [ha4, ha7, ha3, eq1]
  have ha9 : a 9 = 1 := by
    have eq1 := h 4 (by norm_num)
    norm_num at eq1
    linarith [ha5, ha8, ha4, eq1]
  have ha10 : a 10 = 4 := by
    have eq1 := h 5 (by norm_num)
    norm_num at eq1
    linarith [ha6, ha9, ha5, eq1]
  have h2 : ∀ k, a (8 * k + 7) = 17 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha7]
    | succ k ih =>
      have h3 : 8 * (k + 1) + 7 = (8 * k + 15) := by ring
      rw [h3]
      have eq1 := h (8 * k + 10) (by omega)
      simp at eq1
      have eq2 := h (8 * k + 9) (by omega)
      simp at eq2
      have eq3 := h (8 * k + 8) (by omega)
      simp at eq3
      have eq4 := h (8 * k + 7) (by omega)
      simp at eq4
      have eq5 := h (8 * k + 6) (by omega)
      simp at eq5
      have eq6 := h (8 * k + 5) (by omega)
      simp at eq6
      have eq7 := h (8 * k + 4) (by omega)
      simp at eq7
      have eq8 := h (8 * k + 3) (by omega)
      simp at eq8
      have eq9 := h (8 * k + 2) (by omega)
      simp at eq9
      have eq10 := h (8 * k + 1) (by omega)
      simp at eq10
      linarith [ih, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10]
  have h3 : 2023 = 8 * 252 + 7 := by norm_num
  rw [h3]
  exact h2 252