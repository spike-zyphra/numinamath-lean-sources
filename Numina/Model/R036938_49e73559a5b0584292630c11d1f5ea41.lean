import Mathlib

theorem algebra_258055 (Δ : (ℕ → ℝ) → ℕ → ℝ)
  (hΔ : ∀ f n, Δ f n = f (n + 1) - f n)
  (A : ℕ → ℝ) (hΔΔA : ∀ n, Δ (Δ A) n = 1)
    (h1 : A 18 = 0) (h2 : A 91 = 0) : A 0 = 819
  := by

  have h1' : ∀ n, Δ (Δ A) n = 1 := hΔΔA

  have h19 : ∀ n, Δ (Δ A) n = Δ A (n + 1) - Δ A n := by
    intro n
    rw [hΔ]

  have h20 : ∀ n, Δ A n = A (n + 1) - A n := by
    intro n
    rw [hΔ]

  have h3 : ∀ n, Δ A (n + 1) = Δ A n + 1 := by
    intro n
    have eq1n : Δ (Δ A) n = 1 := hΔΔA n
    rw [h19 n] at eq1n
    linarith

  have h4 : ∀ n, Δ A n = Δ A 0 + (n : ℝ) := by
    intro n
    have h5 : ∀ (n : ℕ), Δ A n = Δ A 0 + (n : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h5 : Δ A (n + 1) = Δ A n + 1 := h3 n
        rw [h5]
        rw [ih]
        field_simp
        <;> ring
    specialize h5 n
    simpa using h5

  have eq6 : ∀ n, A n = A 0 + (Δ A 0 : ℝ) * (n : ℝ) + ( (n : ℝ) * (n - 1 : ℝ) ) / 2 := by
    intro n
    have eq7 : ∀ (n : ℕ), A n = A 0 + (Δ A 0 : ℝ) * (n : ℝ) + ( (n : ℝ) * (n - 1 : ℝ) ) / 2 := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h8 : A (n + 1) = A n + Δ A n := by
          have : Δ A n = A (n + 1) - A n := by
            rw [hΔ]
          linarith [this]
        rw [h8]
        rw [ih]
        have h9 : Δ A n = Δ A 0 + (n : ℝ) := h4 n
        rw [h9]
        field_simp
        <;> ring_nf
    specialize eq7 n
    simpa using eq7

  have eq9 : A 18 = A 0 + (Δ A 0 : ℝ) * (18 : ℝ) + ( (18 : ℝ) * (18 - 1 : ℝ) ) / 2 := eq6 18
  have eq10 : A 91 = A 0 + (Δ A 0 : ℝ) * (91 : ℝ) + ( (91 : ℝ) * (91 - 1 : ℝ) ) / 2 := eq6 91

  rw [eq9] at h1
  rw [eq10] at h2

  have eq13 : (Δ A 0 : ℝ) = -54 := by
    nlinarith

  have eq14 : A 0 = 819 := by
    rw [eq13] at eq9
    linarith

  linarith [eq14]