import Mathlib

theorem number_theory_101982 (n : ℤ) :
    ¬ ∃ m, m^2 = n^2 + (n+1)^2 + (n+2)^2 + (n+3)^2 + (n+4)^2 := by
  intro h
  rcases h with ⟨m, hm⟩
  have eq1 : m ^ 2 = 5 * n ^ 2 + 20 * n + 30 := by
    nlinarith
  have eq2 : m ^ 2 = 5 * (n + 2) ^ 2 + 10 := by
    nlinarith
  have h1 : m ^ 2 % 5 = 0 := by
    have h2 : m ^ 2 = 5 * (n + 2) ^ 2 + 10 := eq2
    rw [h2]
    ring_nf
    <;> omega
  have h4 : m % 5 = 0 := by
    have h1' : m ^ 2 % 5 = 0 := h1
    have h5 : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by
      omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h5] at h1'
    <;> tauto
  have h5 : ∃ k, m = 5 * k := by
    refine' ⟨m / 5, by omega⟩
  rcases h5 with ⟨k, hk⟩
  rw [hk] at eq1
  -- Substituting m = 5k, we get 25k^2 = 5n^2 + 20n + 30
  -- Then dividing by 5, get 5k^2 = n^2 + 4n + 6
  have eq4 : 5 * k ^ 2 = n ^ 2 + 4 * n + 6 := by
    nlinarith
  -- Rewrite into (n + 2)^2 + 2 = 5k^2
  have eq5 : (n + 2) ^ 2 + 2 = 5 * k ^ 2 := by
    nlinarith
  have h2 : (n + 2) ^ 2 % 5 = 3 := by
    omega
  have h3 : (n + 2 : ℤ) ^ 2 % 5 = 0 ∨ (n + 2 : ℤ) ^ 2 % 5 = 1 ∨ (n + 2 : ℤ) ^ 2 % 5 = 4 := by
    have h4 : (n + 2) % 5 = 0 ∨ (n + 2) % 5 = 1 ∨ (n + 2) % 5 = 2 ∨ (n + 2) % 5 = 3 ∨ (n + 2) % 5 = 4 := by
      omega
    rcases h4 with (h4 | h4 | h4 | h4 | h4) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h4] at *
  omega