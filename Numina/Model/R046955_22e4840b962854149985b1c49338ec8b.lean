import Mathlib

def A (n : ℕ) := 2^(3*n) + 3^(6*n+2) + 5^(6*n+2)

theorem number_theory_47523 : IsGreatest {x | ∀ i ∈ Finset.range 2000, x ∣ A i} 7 := by
  constructor
  · -- Show that 7 divides all A_i
    intro i hi
    have h1 : i < 2000 := by 
      simp at hi ⊢
      omega
    have h5 : A i % 7 = 0 := by
      dsimp [A]
      have h21 : (2 ^ (3 * i) : ℕ) % 7 = 1 := by
        have h1 : ∀ k : ℕ, (2 ^ (3 * k) : ℕ) % 7 = 1 := by
          intro k 
          induction k with 
          | zero =>
            norm_num 
          | succ k ih =>
            have h9 : 2 ^ (3 * (k + 1)) = (2 ^ (3 * k)) * (2 ^ 3) := by
              ring_nf 
            rw [h9]
            simp [Nat.mul_mod, pow_succ, pow_zero] at ih ⊢ 
            all_goals omega
        apply h1 i 
      have h22 : (3 ^ (6 * i + 2) : ℕ) % 7 = 2 := by
        have h2 : ∀ k : ℕ, (3 ^ (6 * k + 2) : ℕ) % 7 = 2 := by
          intro k 
          induction k with
          | zero =>
            norm_num 
          | succ k ih =>
            have h9 : 3 ^ (6 * (k + 1) + 2) = (3 ^ (6 * k + 2)) * (3 ^ 6) := by
              ring_nf 
            rw [h9]
            simp [Nat.mul_mod, pow_succ, pow_zero] at ih ⊢ 
            all_goals omega 
        apply h2 i 
      have h23 : (5 ^ (6 * i + 2) : ℕ) % 7 = 4 := by
        have h3 : ∀ k : ℕ, (5 ^ (6 * k + 2) : ℕ) % 7 = 4 := by
          intro k 
          induction k with 
          | zero =>
            norm_num 
          | succ k ih =>
            have h9 : 5 ^ (6 * (k + 1) + 2) = (5 ^ (6 * k + 2)) * (5 ^ 6) := by
              ring_nf 
            rw [h9]
            simp [Nat.mul_mod, pow_succ, pow_zero] at ih ⊢ 
            all_goals omega 
        apply h3 i 
      omega 
    have h6 : 7 ∣ A i := by 
      omega 
    simpa using h6 
  · -- Show the greatest.
    intro x hx 
    have h1 : ∀ i ∈ Finset.range 2000, x ∣ A i := hx
    have h2 := h1 0 (by simp)
    have hA0 : A 0 = 35 := by
      norm_num [A] 
    rw [hA0] at h2 
    have h3 := h1 1 (by simp)
    have hA1 : A 1 = 397194 := by
      norm_num [A] 
    rw [hA1] at h3 
    have h4 : x ∣ 7 := by 
      exact Nat.dvd_gcd h2 h3 
    have h5 : x ≤ 7 := by 
      exact Nat.le_of_dvd (show 0 < 7 by norm_num) h4 
    linarith