import Mathlib

theorem algebra_16619 {a : ℕ → ℝ} (ha1 : a 1 = 2007) (ha2 : a 2 = 2008)
    (han : ∀ n ≥ 1, a n + a (n + 1) + a (n + 2) = n) :
    a 1000 = 2340 := by

  have h1 : ∀ n ≥ 1, a (n + 3) = a n + 1 := by
    intro n hn
    have eq1 := han n hn
    have eq2 := han (n + 1) (by linarith)
    simp [show n ≥ 1 by linarith] at eq1 eq2 ⊢
    nlinarith

  have h2 : ∀ k, a (3 * k + 1) = 2007 + (k : ℝ) := by
    intro k
    induction k with
    | zero =>
      norm_num [ha1]
    | succ k ih =>
      have eq3 : a (3 * (k + 1 : ℕ) + 1) = a (3 * k + 1) + 1 := by
        specialize h1 (3 * k + 1) (by omega)
        simp [show 3 * k + 1 + 3 = 3 * (k + 1 : ℕ) + 1 by omega] at h1 ⊢
        linarith
      rw [eq3]
      rw [ih]
      all_goals
        simp [add_assoc]
        <;> ring

  have eq1000 : a 1000 = 2340 := by
    specialize h2 333
    norm_num at h2 ⊢
    linarith

  linarith [eq1000]