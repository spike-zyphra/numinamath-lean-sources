import Mathlib

theorem number_theory_275357 (a b c : ℤ) (h₀ : Odd (a + b + c)) :
    Odd a ∨ Odd b ∨ Odd c := by
  by_contra h
  push_neg at h 
  rcases h with ⟨ha, hb, hc⟩ 
  have h1 : Even a := by 
    simpa using ha
  have h2 : Even b := by 
    simpa using hb
  have h3 : Even c := by 
    simpa using hc
  have h4 : Even (a + b + c) := by
    have h5 : Even a := h1
    have h6 : Even b := h2
    have h7 : Even c := h3
    obtain ⟨k₁, hk₁⟩ := h5
    obtain ⟨k₂, hk₂⟩ := h6
    obtain ⟨k₃, hk₃⟩ := h7
    use k₁ + k₂ + k₃
    linarith
  have h5 : ¬Odd (a + b + c) := by
    rw [Int.not_odd_iff_even]
    exact h4
  contradiction