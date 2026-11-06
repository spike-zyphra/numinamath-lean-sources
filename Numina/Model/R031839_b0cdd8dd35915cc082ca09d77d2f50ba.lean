import Mathlib

theorem algebra_159051 (a : ℕ → ℤ) (h₀ : a 1 = 2) (h₁ : ∀ n, a (n + 1) = a n ^ 2 - 2 * a n + 1) :
    a 2020 = 1 := by

  have ha2 : a 2 = 1 := by
    specialize h₁ 1
    rw [h₀] at h₁
    norm_num at h₁
    linarith

  have ha3 : a 3 = 0 := by
    specialize h₁ 2
    rw [ha2] at h₁
    norm_num at h₁
    linarith

  have ha4 : a 4 = 1 := by
    specialize h₁ 3
    rw [ha3] at h₁
    norm_num at h₁
    linarith

  have h2 : ∀ (n : ℕ), a (2 * n + 3) = 0 ∧ a (2 * n + 4) = 1 := by
    intro n
    induction n with
    | zero =>
      constructor
      · -- Prove a 3 = 0
        exact ha3
      · -- Prove a 4 = 1
        exact ha4
    | succ n ih =>
      have h3 : a (2 * n + 5) = 0 := by
        have eq1 : a (2 * n + 5) = a (2 * n + 4) ^ 2 - 2 * a (2 * n + 4) + 1 := by
          specialize h₁ (2 * n + 4)
          simpa using h₁
        have h4 : a (2 * n + 4) = 1 := by
          linarith [ih.2]
        rw [h4] at eq1
        norm_num at eq1
        linarith
      have h4 : a (2 * n + 6) = 1 := by
        have eq2 : a (2 * n + 6) = a (2 * n + 5) ^ 2 - 2 * a (2 * n + 5) + 1 := by
          specialize h₁ (2 * n + 5)
          simpa using h₁
        have h5 : a (2 * n + 5) = 0 := by
          linarith [h3]
        rw [h5] at eq2
        norm_num at eq2
        linarith
      constructor
      · -- Prove a (2 * (n + 1) + 3) = 0
        simpa using h3
      · -- Prove a (2 * (n + 1) + 4) = 1
        simpa using h4

  have h3 : 2020 = 2 * 1008 + 4 := by
    omega
  have h4 : a 2020 = 1 := by
    rw [h3]
    have h5 := (h2 1008).2
    simpa using h5
  exact h4