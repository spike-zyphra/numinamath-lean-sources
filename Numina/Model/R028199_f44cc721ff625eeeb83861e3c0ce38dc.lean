import Mathlib

theorem algebra_111288 (x : ℕ → ℝ) (h : ∀ n, x n + x (n + 1) + x (n + 2) = 20)
    (hx1 : x 1 = 9) (hx12 : x 12 = 7) :
    x 2000 = 4 := by

  have eq1 : x 0 + x 2 = 11 := by
    have eq11 := h 0
    simp [hx1] at eq11
    linarith

  have eq2_x3 : x 3 = x 0 := by
    have eq11 := h 0
    have eq22 := h 1
    simp at eq11 eq22
    linarith [hx1]

  have eq5 : ∀ n : ℕ, x (n + 3) = x n := by
    intro n 
    have eq11 := h n 
    have eq22 := h (n + 1)
    simp [show (n + 1 : ℕ) + 1 = n + 2 by omega, show (n + 1 : ℕ) + 2 = n + 3 by omega] at eq22
    linarith

  have eq_x0 : x 0 = 7 := by
    have h0 : x 12 = x 0 := by
      have eq13 : x 12 = x 9 := by 
        rw [show 12 = 9 + 3 by norm_num]
        rw [eq5 9]
      have eq16 : x 9 = x 6 := by
        rw [show 9 = 6 + 3 by norm_num]
        rw [eq5 6]
      have eq19 : x 6 = x 3 := by 
        rw [show 6 = 3 + 3 by norm_num]
        rw [eq5 3]
      have eq112 : x 3 = x 0 := by 
        rw [show 3 = 0 + 3 by norm_num]
        rw [eq5 0]
      linarith [eq13, eq16, eq19, eq112]
    linarith [h0, hx12]

  have eq_x2 : x 2 = 4 := by
    linarith [eq1, eq_x0]

  have h2000 : x 2000 = x 2 := by
    have eq5' : ∀ (k : ℕ), x (3 * k + 2) = x 2 := by
      intro k 
      induction k with 
      | zero =>
        simp 
      | succ k ih =>
        have eq6_1 : 3 * (k + 1) + 2 = (3 * k + 2) + 3 := by ring
        rw [eq6_1]
        have eq7_1 : x ((3 * k + 2) + 3) = x (3 * k + 2) := by
          specialize eq5 (3 * k + 2)
          simpa using eq5
        rw [eq7_1, ih]
    specialize eq5' 666 
    norm_num at eq5' ⊢ 
    linarith

  linarith [h2000, eq_x2]