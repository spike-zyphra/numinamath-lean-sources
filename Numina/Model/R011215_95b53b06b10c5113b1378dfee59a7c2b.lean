import Mathlib

theorem algebra_231021 (a : ℕ → ℝ) (h₀ : a 4 = 1) (h₁ : a 11 = 9)
    (h₂ : ∀ n, a n + a (n + 1) + a (n + 2) = 15) :
    a 2016 = 5 := by

  have eq1 := h₂ 0
  simp [show (0 : ℕ) + 1 = 1 by omega, show (0 : ℕ) + 2 = 2 by omega] at eq1
  have eq2 := h₂ 1
  simp [show (1 : ℕ) + 1 = 2 by omega, show (1 : ℕ) + 2 = 3 by omega] at eq2
  have eq3 := h₂ 2
  simp [show (2 : ℕ) + 1 = 3 by omega, show (2 : ℕ) + 2 = 4 by omega] at eq3
  have eq4 := h₂ 3
  simp [show (3 : ℕ) + 1 = 4 by omega, show (3 : ℕ) + 2 = 5 by omega] at eq4
  have eq5 := h₂ 4
  simp [show (4 : ℕ) + 1 = 5 by omega, show (4 : ℕ) + 2 = 6 by omega] at eq5
  have eq6 := h₂ 5
  simp [show (5 : ℕ) + 1 = 6 by omega, show (5 : ℕ) + 2 = 7 by omega] at eq6
  have eq7 := h₂ 6
  simp [show (6 : ℕ) + 1 = 7 by omega, show (6 : ℕ) + 2 = 8 by omega] at eq7
  have eq8 := h₂ 7
  simp [show (7 : ℕ) + 1 = 8 by omega, show (7 : ℕ) + 2 = 9 by omega] at eq8
  have eq9 := h₂ 8
  simp [show (8 : ℕ) + 1 = 9 by omega, show (8 : ℕ) + 2 = 10 by omega] at eq9
  have eq10 := h₂ 9
  simp [show (9 : ℕ) + 1 = 10 by omega, show (9 : ℕ) + 2 = 11 by omega] at eq10
  have eq11 := h₂ 10
  simp [show (10 : ℕ) + 1 = 11 by omega, show (10 : ℕ) + 2 = 12 by omega] at eq11
  have eq12 := h₂ 11
  simp [show (11 : ℕ) + 1 = 12 by omega, show (11 : ℕ) + 2 = 13 by omega] at eq12

  have eq13 : a 3 = a 0 := by
    nlinarith
  have eq14 : a 2 + a 0 = 14 := by
    nlinarith
  have eq15 : a 5 = 15 - a 0 - 1 := by 
    have eq_16 : a 3 + a 4 + a 5 = 15 := by linarith 
    rw [show a 3 = a 0 by linarith [eq13]] at eq_16
    linarith 
  have eq16 : a 5 + a 6 = 14 := by 
    linarith 
  have eq17 : a 6 = 15 - a 5 - a 7 := by 
    linarith

  have h3 : ∀ k : ℕ, a (6 * k) = a 0 := by
    intro k 
    induction k with
    | zero =>
      simp 
    | succ k ih =>
      have eq1 := h₂ (6 * k)
      simp [show (6 * k : ℕ) + 1 = (6 * k + 1 : ℕ) by omega, show (6 * k : ℕ) + 2 = (6 * k + 2 : ℕ) by omega] at eq1
      have eq2 := h₂ (6 * k + 1)
      simp [show (6 * k + 1 : ℕ) + 1 = (6 * k + 2 : ℕ) by omega, show (6 * k + 1 : ℕ) + 2 = (6 * k + 3 : ℕ) by omega] at eq2
      have eq3 := h₂ (6 * k + 2)
      simp [show (6 * k + 2 : ℕ) + 1 = (6 * k + 3 : ℕ) by omega, show (6 * k + 2 : ℕ) + 2 = (6 * k + 4 : ℕ) by omega] at eq3
      have eq4 := h₂ (6 * k + 3)
      simp [show (6 * k + 3 : ℕ) + 1 = (6 * k + 4 : ℕ) by omega, show (6 * k + 3 : ℕ) + 2 = (6 * k + 5 : ℕ) by omega] at eq4
      have eq5 := h₂ (6 * k + 4)
      simp [show (6 * k + 4 : ℕ) + 1 = (6 * k + 5 : ℕ) by omega, show (6 * k + 4 : ℕ) + 2 = (6 * k + 6 : ℕ) by omega] at eq5
      have eq6 := h₂ (6 * k + 5)
      simp [show (6 * k + 5 : ℕ) + 1 = (6 * k + 6 : ℕ) by omega, show (6 * k + 5 : ℕ) + 2 = (6 * k + 7 : ℕ) by omega] at eq6
      have eq7 : a (6 * (k + 1)) = a (6 * k + 6) := by ring_nf 
      have eq18 := h₂ (6 * k + 6)
      simp [show (6 * k + 6 : ℕ) + 1 = (6 * k + 7 : ℕ) by omega, show (6 * k + 6 : ℕ) + 2 = (6 * k + 8 : ℕ) by omega] at eq18
      have eq19 := h₂ (6 * k + 7)
      simp [show (6 * k + 7 : ℕ) + 1 = (6 * k + 8 : ℕ) by omega, show (6 * k + 7 : ℕ) + 2 = (6 * k + 9 : ℕ) by omega] at eq19
      have eq20 := h₂ (6 * k + 8)
      simp [show (6 * k + 8 : ℕ) + 1 = (6 * k + 9 : ℕ) by omega, show (6 * k + 8 : ℕ) + 2 = (6 * k + 10 : ℕ) by omega] at eq20
      have eq21 := h₂ (6 * k + 9)
      simp [show (6 * k + 9 : ℕ) + 1 = (6 * k + 10 : ℕ) by omega, show (6 * k + 9 : ℕ) + 2 = (6 * k + 11 : ℕ) by omega] at eq21
      have eq22 := h₂ (6 * k + 10)
      simp [show (6 * k + 10 : ℕ) + 1 = (6 * k + 11 : ℕ) by omega, show (6 * k + 10 : ℕ) + 2 = (6 * k + 12 : ℕ) by omega] at eq22
      have eq23 := h₂ (6 * k + 11)
      simp [show (6 * k + 11 : ℕ) + 1 = (6 * k + 12 : ℕ) by omega, show (6 * k + 11 : ℕ) + 2 = (6 * k + 13 : ℕ) by omega] at eq23
      have eq8 : a (6 * k + 6) = a 0 := by 
        linarith [eq1, eq2, eq3, eq4, eq5, eq6, eq18, eq19, eq20, eq21, eq22, eq23, ih, eq13]
      rw [eq7, eq8]

  have h2016 : a 2016 = a 0 := by 
    specialize h3 336
    have h4 : (2016 : ℕ) = 6 * 336 := by omega 
    rw [h4] at *
    linarith

  -- The kernel idea here is to provide all available linear information for solving a 2016, x, and particularly with information added to the induction step.
  have h5 : a 0 = 5 := by
    nlinarith [h₀, h₁, eq1, eq2, eq3, eq4, eq5, eq6, eq7, eq8, eq9, eq10, eq11, eq12, eq13, eq14, eq15, eq16, eq17]

  linarith [h2016, h5]