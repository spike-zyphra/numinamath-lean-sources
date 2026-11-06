import Mathlib

theorem algebra_313115 {f : ℕ → ℕ} (hf1 : f 1 = 2)
    (hfeven : ∀ n > 1, Even n → f n = f (n - 1) + 2)
    (hfinv : ∀ n > 1, Odd n → f n = f (n - 2) + 2) :
    f 2017 = 2018 := by

  have h1 : ∀ k, f (2 * k + 1) = 2 * k + 2 := by
    intro k
    induction k with
    | zero =>
      simp [hf1]
    | succ k ih =>
      have eq1 : f (2 * (k + 1) + 1) = f (2 * k + 1) + 2 := by
        have h3 : (2 * (k + 1) + 1 : ℕ) > 1 := by
          omega
        have h2 : Odd (2 * (k + 1) + 1 : ℕ) := by
          simp [Nat.odd_iff]
          <;> omega
        have h4 : f (2 * (k + 1) + 1 : ℕ) = f ((2 * (k + 1) + 1 : ℕ) - 2) + 2 := by 
          apply hfinv (2 * (k + 1) + 1 : ℕ) (by omega) h2 
        have h5 : ((2 * (k + 1) + 1 : ℕ) - 2 : ℕ) = (2 * k + 1 : ℕ) := by
          omega
        rw [h4, h5]
      rw [eq1]
      omega
  have eq2 : f 2017 = 2018 := by 
    specialize h1 1008
    norm_num at h1 ⊢
    omega
  exact eq2