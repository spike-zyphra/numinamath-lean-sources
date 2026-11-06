import Mathlib

theorem number_theory_240347 (n : ℕ) (h₀ : Even n) (h₁ : ¬ 4 ∣ n) :
    ¬∃ k, Odd k ∧ Odd (k + 2) ∧ n = k + (k + 2) := by 
  rintro ⟨k, ⟨hk1, hk2, hn⟩⟩
  have h2 : n = 2 * (k + 1) := by
    omega
  have h3 : Odd k := hk1
  rcases h3 with ⟨a, ha⟩
  have h4 : k + 1 = 2 * (a + 1) := by
    omega
  have h5 : 4 ∣ n := by
    rw [h2]
    omega
  contradiction