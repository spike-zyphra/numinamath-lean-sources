import Mathlib

theorem algebra_12959 {a : ℕ → ℤ} (ha : ∀ n > 0, 2 * a (n + 2) = a (n + 1) + 15 * a n)
    (ha1 : a 1 = 1) (ha2 : a 2 = 3) :
    a 2019 / a 2015 = 81 := by

  have h1 : ∀ n : ℕ, a (n + 1) = 3 ^ n := by
    intro n 
    induction' n using Nat.twoStepInduction with n ih1 ih2
    · -- Base case: n = 0
      simp [ha1]
    · -- Base case: n = 1 
      simp [ha2]
    · -- Inductive step: Assume it holds for n and n+1, prove for n+2
      have h2 := ha (n + 1) (by linarith)
      simp [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega] at h2 ⊢
      rw [ih2, ih1] at h2
      have eq1 : 2 * a (n + 3) = 2 * (3 ^ (n + 2) : ℤ) := by 
        have eq2 : (3 ^ (n + 1) + 15 * 3 ^ n : ℤ) = 2 * (3 ^ (n + 2) : ℤ) := by 
          ring_nf
        linarith [h2, eq2]
      have h3 : a (n + 3) = 3 ^ (n + 2) := by 
        linarith 
      exact h3

  have h_eq1 : a 2019 = 3 ^ 2018 := by 
    specialize h1 2018 
    norm_num at h1 ⊢ 
    omega

  have h_eq2 : a 2015 = 3 ^ 2014 := by 
    specialize h1 2014 
    norm_num at h1 ⊢ 
    omega

  rw [h_eq1, h_eq2] 
  norm_num