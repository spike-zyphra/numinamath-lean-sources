import Mathlib

open Real

lemma lemma_1 (a : ℕ → ℝ)
    (h₀ : a 1 = 1)
    (h₁ : a 2 = Real.sqrt 19)
    (h₂ : ∀ n ≥ 2, a (n + 1) + a n + a (n - 1) = 3 * n) :
    ∀ k, a (3 * k + 1) = 3 * k + 1 := by
  intro k
  induction k with
  | zero =>
    norm_num [h₀]
  | succ k ih =>
    have eq1 := h₂ (3 * k + 2) (by omega)
    have eq2 := h₂ (3 * k + 3) (by omega)
    have eq3 : a (3 * k + 3) + a (3 * k + 2) + a (3 * k + 1) = 3 * (3 * k + 2 : ℝ) := by
      have h3 : (3 * k + 2 : ℕ) ≥ 2 := by
        omega
      have eq1' := h₂ (3 * k + 2) (by omega)
      simp [show 3 * k + 2 + 1 = 3 * k + 3 by omega, 
            show (3 * k + 2 : ℕ) = 3 * k + 2 by omega, 
            show (3 * k + 2 - 1 : ℕ) = 3 * k + 1 by
              omega
            ] at eq1'
      linarith
    have eq4 : a (3 * k + 4) + a (3 * k + 3) + a (3 * k + 2) = 3 * (3 * k + 3 : ℝ) := by
      have h4 : (3 * k + 3 : ℕ) ≥ 2 := by
        omega
      have eq2' := h₂ (3 * k + 3) (by omega)
      simp [show 3 * k + 3 + 1 = 3 * k + 4 by omega, 
            show (3 * k + 3 : ℕ) = 3 * k + 3 by omega, 
            show (3 * k + 3 - 1 : ℕ) = 3 * k + 2 by
              omega
            ] at eq2'
      linarith
    have eq5 : a (3 * k + 4) = a (3 * k + 1) + 3 := by
      linarith [eq3, eq4]
    have eq6 : a (3 * (k + 1) + 1) = 3 * (k + 1 : ℝ) + 1 := by
      have h7 : 3 * (k + 1) + 1 = 3 * k + 4 := by
        omega
      rw [h7]
      linarith [eq5, ih]
    simpa using eq6


theorem algebra_224886 {a : ℕ → ℝ} (ha1 : a 1 = 1) (ha2 : a 2 = sqrt 19)
    (han : ∀ n ≥ 2, a (n + 1) + a n + a (n - 1) = 3 * n) :
    a 2011 = 2011 := by
  have lemma_1 : ∀ k, a (3 * k + 1) = 3 * k + 1 := by
    intro k
    induction k with
    | zero =>
      norm_num [ha1]
    | succ k ih =>
      have eq1 := han (3 * k + 2) (by omega)
      have eq2 := han (3 * k + 3) (by omega)
      have eq3 : a (3 * k + 3) + a (3 * k + 2) + a (3 * k + 1) = 3 * (3 * k + 2 : ℝ) := by
        have h3 : (3 * k + 2 : ℕ) ≥ 2 := by
          omega
        have eq1' := han (3 * k + 2) (by omega)
        simp [show 3 * k + 2 + 1 = 3 * k + 3 by omega, 
              show (3 * k + 2 : ℕ) = 3 * k + 2 by omega, 
              show (3 * k + 2 - 1 : ℕ) = 3 * k + 1 by
                omega
              ] at eq1'
        linarith
      have eq4 : a (3 * k + 4) + a (3 * k + 3) + a (3 * k + 2) = 3 * (3 * k + 3 : ℝ) := by
        have h4 : (3 * k + 3 : ℕ) ≥ 2 := by
          omega
        have eq2' := han (3 * k + 3) (by omega)
        simp [show 3 * k + 3 + 1 = 3 * k + 4 by omega, 
              show (3 * k + 3 : ℕ) = 3 * k + 3 by omega, 
              show (3 * k + 3 - 1 : ℕ) = 3 * k + 2 by
                omega
              ] at eq2'
        linarith
      have eq5 : a (3 * k + 4) = a (3 * k + 1) + 3 := by
        linarith [eq3, eq4]
      have eq6 : a (3 * (k + 1) + 1) = 3 * (k + 1 : ℝ) + 1 := by
        have h7 : 3 * (k + 1) + 1 = 3 * k + 4 := by
          omega
        rw [h7]
        linarith [eq5, ih]
      simpa using eq6
  have h2011 : 2011 = 3 * 670 + 1 := by
    omega
  rw [h2011]
  specialize lemma_1 670
  norm_num at lemma_1 ⊢
  linarith [lemma_1]