import Mathlib

theorem algebra_147393 (a : ℕ → ℝ) (h₀ : a 4 = 1) (h₁ : a 11 = 9)
    (h₂ : ∀ n, a n + a (n + 1) + a (n + 2) = 15) :
    a 2016 = 5 := by

  have h3 : ∀ n, a (n + 3) = a n := by
    intro n
    have eq1 := h₂ n
    have eq2 := h₂ (n + 1)
    simp [show n + 1 + 1 = n + 2 by omega, show n + 1 + 2 = n + 3 by omega] at eq2
    linarith

  have h4 : a 1 = 1 := by
    have h5 : a 4 = a 1 := by
      rw [show 4 = 1 + 3 by omega]
      rw [h3 1]
    rw [h₀] at h5
    linarith

  have h5 : a 2 = 9 := by
    have h6 : a 11 = a 2 := by
      have h7 : a 11 = a 8 := by
        rw [show 11 = 8 + 3 by omega]
        rw [h3 8]
      have h8 : a 8 = a 5 := by
        rw [show 8 = 5 + 3 by omega]
        rw [h3 5]
      have h9 : a 5 = a 2 := by
        rw [show 5 = 2 + 3 by omega]
        rw [h3 2]
      rw [h7, h8, h9]
    rw [h₁] at h6
    linarith

  have h6 : a 0 = 5 := by
    have eq1 := h₂ 0
    simp [h4, h5] at eq1
    linarith

  have h7 : ∀ k, a (3 * k) = a 0 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      calc
        a (3 * (k + 1)) = a (3 * k + 3) := by ring_nf
        _ = a (3 * k) := by rw [show 3 * k + 3 = (3 * k) + 3 by ring]; rw [h3]
        _ = a 0 := by rw [ih]

  have h8 : a 2016 = a 0 := by
    calc
      a 2016 = a (3 * 672) := by norm_num
      _ = a 0 := by rw [h7 672]

  rw [h8, h6]