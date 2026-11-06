import Mathlib

theorem number_theory_325355 (a : ℕ → ℕ) (d : ℕ) (h₀ : ∀ n, a n = a 0 + d * n)
    (h₁ : ∀ n m, a n > 0 ∧ a m > 0) (h₂ : d > 0) (h₃ : ∀ n m, a n + a m ∈ Set.range a)
    (h₄ : a 0 = 6) :
    d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 6 := by
  have h5 : a 0 + a 0 ∈ Set.range a := h₃ 0 0
  rw [h₄] at h5
  rcases h5 with ⟨k, hk⟩
  have h6 : a k = 12 := by
    linarith
  have h7 : a k = a 0 + d * k := h₀ k
  rw [h₄] at h7
  rw [h7] at h6
  have h8 : d * k = 6 := by 
    omega
  have h9 : d ∣ 6 := by
    use k
    linarith
  have h10 : d ≤ 6 := by
    exact Nat.le_of_dvd (by norm_num) h9
  interval_cases d <;> omega