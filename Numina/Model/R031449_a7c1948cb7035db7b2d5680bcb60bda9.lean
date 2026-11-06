import Mathlib

theorem algebra_297071 (n : ℕ) (h₀ : n ∈ Finset.Icc 1000 9999) (h₁ : (n / 10) % 10 - 1 = n % 10)
    (h₂ : n % 10 + 2 = (n / 100) % 10) (h₃ : n + (1000 * (n % 10) + 100 * ((n / 10) % 10) +
      10 * ((n / 100) % 10) + (n / 1000)) = 9878) :
    n = 1987 := by
  have h4 : n ≥ 1000 := by
    simp [Finset.mem_Icc] at h₀
    omega
  have h5 : n ≤ 9999 := by
    simp [Finset.mem_Icc] at h₀
    omega

  have eq1 : n % 10 < 10 := by
    omega

  have eq2 : (n / 10) % 10 < 10 := by
    omega

  have eq3 : (n / 100) % 10 < 10 := by
    omega

  have eq4 : n / 1000 < 10 := by
    omega

  interval_cases h6 : n % 10 <;> interval_cases h7 : (n / 10) % 10 <;> interval_cases h8 : (n / 100) % 10 <;> 
    omega