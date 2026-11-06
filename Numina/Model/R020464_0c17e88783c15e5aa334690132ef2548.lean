import Mathlib

theorem number_theory_244171 {n : ℕ} (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : n = (100 * (n % 100) + n / 100) + 594)
    (h₂ : (n / 100) ^ 2 - (n % 100) ^ 2 = 204) :
    n = 2014 := by 
  have h3 : n ≥ 1000 := by 
    simp [Finset.mem_Icc] at h₀ 
    omega 
  have h4 : n ≤ 9999 := by 
    simp [Finset.mem_Icc] at h₀ 
    omega 
  have eq2a : n % 100 ≤ 99 := by 
    omega 
  have eq3a : n / 100 ≤ 99 := by 
    omega 
  have eq2b : (n / 100 : ℕ) ^ 2 = (n % 100 : ℕ) ^ 2 + 204 := by 
    omega 
  have eq1 : 99 * (n / 100 : ℕ) = 99 * (n % 100 : ℕ) + 594 := by
    -- This equation is obtained from h₁ and the identity `n = 100*(n/100) + (n%100)`.
    have h5 : n = 100 * (n / 100) + (n % 100) := by 
      omega 
    have h5a : n = 100 * (n % 100) + (n / 100) + 594 := by
      linarith [h₁]
    omega 
  have eq1_a : n / 100 = (n % 100) + 6 := by 
    omega 
  have hx2 : n % 100 = 14 := by 
    rw [show n / 100 = n % 100 + 6 by omega] at eq2b 
    nlinarith 
  have hx1 : n / 100 = 20 := by 
    omega 
  have h7 : n = 2014 := by 
    omega 
  exact h7