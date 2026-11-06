import Mathlib

theorem algebra_279491 {n m : ℕ} (h₀ : n ∈ Finset.Icc 10 99) (h₁ : m ∈ Finset.Icc 10 99)
    (h₂ : n / 10 = m / 10) :
    n * m = (n / 10 * 10) * ((n / 10 * 10) + (n % 10) + (m % 10)) + (n % 10) * (m % 10) := by 
  simp only [Finset.mem_Icc] at h₀ h₁ 
  rcases h₀ with ⟨hn1, hn2⟩
  rcases h₁ with ⟨hm1, hm2⟩
  have eq_n : n = 10 * (n / 10) + (n % 10) := by 
    omega
  have eq_m : m = 10 * (m / 10) + (m % 10) := by 
    omega
  have h3 : m / 10 = n / 10 := by
    omega
  calc 
    n * m = ((10 * (n / 10) + (n % 10)) ) * ((10 * (m / 10) + (m % 10)) ) := by 
      rw [show (10 * (n / 10) + (n % 10)) = n by omega, show (10 * (m / 10) + (m % 10)) = m by omega]
    _ = (n / 10 * 10) * ((n / 10 * 10) + (n % 10) + (m % 10)) + (n % 10) * (m % 10) := by
      rw [h3]
      ring_nf