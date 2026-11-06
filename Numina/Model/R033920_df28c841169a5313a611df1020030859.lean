import Mathlib

theorem number_theory_290142 (x y : ℕ → ℤ) (hx1 : x 1 = 1) (hy1 : y 1 = 1)
    (hxn : ∀ k ≥ 2, x k = x (k - 1) + 1 - 5 * ⌊(k - 1) / 5⌋₊ + 5 * ⌊(k - 2) / 5⌋₊)
    (hy : ∀ k ≥ 2, y k = y (k - 1) + ⌊(k - 1) / 5⌋₊ - ⌊(k - 2) / 5⌋₊) :
    x 2008 = 3 ∧ y 2008 = 402 := by

  have x2008 : x 2008 = 3 := by 
    have h1 : ∀ (k : ℕ), x (k + 1) = 1 + (k : ℤ) - 5 * ((k : ℤ) / 5) := by
      intro k
      induction k with 
      | zero =>
        simp [hx1]
      | succ k ih =>
        have eq2 := hxn ((k + 2 : ℕ)) (by linarith)
        simp [show (k + 2 : ℕ) - 1 = k + 1 by omega, show (k + 2 : ℕ) - 2 = k by omega] at eq2 ⊢
        rw [eq2]
        omega 
    have h2 := h1 2007
    norm_num at h2 ⊢
    omega

  have y2008 : y 2008 = 402 := by 
    have h1 : ∀ (k : ℕ), y (k + 1) = 1 + ((k : ℤ) / 5) := by 
      intro k 
      induction k with 
      | zero => 
        simp [hy1]
      | succ k ih =>
        have eq2 := hy ((k + 2 : ℕ)) (by linarith)
        simp [show (k + 2 : ℕ) - 1 = k + 1 by omega, show (k + 2 : ℕ) - 2 = k by omega] at eq2 ⊢
        rw [eq2]
        omega 
    have h2 := h1 2007
    norm_num at h2 ⊢
    omega
  constructor 
  · exact x2008
  · exact y2008