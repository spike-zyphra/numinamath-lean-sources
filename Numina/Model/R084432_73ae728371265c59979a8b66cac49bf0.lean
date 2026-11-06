import Mathlib

theorem number_theory_196936 (n : ℕ) (h₀ : n < 1000000) (h₁ : n > 99999)
    (h₂ : (n / 1000) % 1000 = n % 1000) :
    7 ∣ n ∧ 11 ∣ n ∧ 13 ∣ n := by 
  -- We can derive that the first three digits equal the last three digits, so the number is 1001 multiplied by the first three digits
  -- Let omega handle the deduction of n = 1001 * (n / 1000)
  have h3 : n = 1001 * (n / 1000) := by
    omega
  -- Now we need to prove 7, 11, 13 all divide n
  have h4 : 7 ∣ n := by
    rw [h3]
    omega
  have h5 : 11 ∣ n := by
    rw [h3]
    omega
  have h6 : 13 ∣ n := by
    rw [h3]
    omega
  exact ⟨h4, h5, h6⟩