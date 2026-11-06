import Mathlib

theorem number_theory_172204 (n : ℕ) (h₀ : n ∈ Finset.Icc 100000 999999) (h₁ : (n / 1000) % 1000 = n % 1000) :
    7 ∣ n ∧ 11 ∣ n ∧ 13 ∣ n := by
  have h2 : n ≥ 100000 := Finset.mem_Icc.mp h₀ |>.1
  have h3 : n ≤ 999999 := Finset.mem_Icc.mp h₀ |>.2
  have h4 : n = 1001 * (n / 1000) := by
    have h1' : n / 1000 = n % 1000 := by
      have h1 : (n / 1000) % 1000 = n % 1000 := h₁
      have h2 : n / 1000 < 1000 := by
        have h3 : n < 1000000 := by linarith
        have h4 : n / 1000 < 1000 := by
          omega
        exact h4
      have h3 : (n / 1000) % 1000 = n / 1000 := by
        omega
      rw [h3] at h1
      omega
    omega
  have h5 : 7 ∣ n := by
    rw [h4]
    omega
  have h6 : 11 ∣ n := by
    rw [h4]
    omega
  have h7 : 13 ∣ n := by
    rw [h4]
    omega
  exact ⟨h5, h6, h7⟩