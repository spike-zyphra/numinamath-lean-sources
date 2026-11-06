import Mathlib

theorem number_theory_254221 (m c : ℕ) (h₀ : m + c = 200) (h₁ : m < 100)
    (h₂ : m > (4 / 5 : ℚ) * c) (h₃ : 8 ∣ m) (h₄ : 8 ∣ c) :
    m = 96 ∧ c = 104 := by
  have h5 : (m : ℚ) > (4 / 5 : ℚ) * c := by 
    simpa using h₂
  have h6 : (5 * (m : ℚ) > 4 * (c : ℚ)) := by
    linarith
  have h7 : 5 * (m : ℕ) > 4 * (c : ℕ) := by
    exact_mod_cast h6
  have h8 : c = 200 - m := by 
    omega
  rw [h8] at h7
  have h9 : m > 88 := by 
    omega
  have h10 : m ≤ 99 := by
    omega
  have h11 : m = 96 := by 
    omega
  have h12 : c = 104 := by 
    omega
  exact ⟨h11, h12⟩