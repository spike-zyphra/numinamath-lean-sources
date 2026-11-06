import Mathlib

theorem number_theory_51968 : ∀ n : ℤ, ¬ 121 ∣ n^2 + 2 * n + 12 := by
  intro n h
  have h1 : (n ^ 2 + 2 * n + 12) % 121 = 0 := by 
    omega
  have h2 : (n + 1) ^ 2 % 121 = 110 := by
    have h3 : (n ^ 2 + 2 * n + 12) % 121 = 0 := h1
    have : n^2 + 2 * n + 12 = (n + 1) ^ 2 + 11 := by
      nlinarith
    rw [this] at h3 
    omega
  have h3 : (n + 1) % 11 = 0 := by
    have h4 : (n + 1) ^ 2 % 11 = 0 := by
      have h5 : (n + 1) ^ 2 % 121 = 110 := h2
      omega
    have h6 : (n + 1) % 11 = 0 ∨ (n + 1) % 11 = 1 ∨ (n + 1) % 11 = 2 ∨ (n + 1) % 11 = 3 ∨ (n + 1) % 11 = 4 ∨ (n + 1) % 11 = 5 ∨ (n + 1) % 11 = 6 ∨ (n + 1) % 11 = 7 ∨ (n + 1) % 11 = 8 ∨ (n + 1) % 11 = 9 ∨ (n + 1) % 11 = 10 := by
      omega
    rcases h6 with (h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6 | h6) <;> 
      simp [pow_two, Int.add_emod, Int.mul_emod, h6] at h4 <;> tauto
  have h4 : ∃ k : ℤ, n + 1 = 11 * k := by 
    refine' ⟨(n + 1) / 11, by omega⟩
  rcases h4 with ⟨k, hk⟩
  have h5 : (n + 1 : ℤ) = 11 * k := by linarith 
  have h6 : (n + 1 : ℤ) ^ 2 = 121 * (k ^ 2) := by 
    rw [h5]
    nlinarith
  omega