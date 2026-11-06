import Mathlib

theorem number_theory_105497 (a b : ℕ) (ha : a < 10) (hb : b < 10) :
    5 ∣ (a * 1000 + b * 100 + 60) + 25 * (a * 10 + b) ∧
    (a * 1000 + b * 100 + 60) + 25 * (a * 10 + b) % 25 = 10 ∧
    Even b → ∃ m, m^2 = 2^(a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) := by 
  intro h 
  rcases h with ⟨h1, h2, heven⟩
  have h3 : (a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) % 2 = 0 := by
    have h4 : b % 2 = 0 := by 
      obtain ⟨k, hk⟩ := heven 
      omega 
    omega 
  have h5 : ∃ k, (a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) = 2 * k := by 
    have h8 : (a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) % 2 = 0 := by 
      obtain ⟨k, hk⟩ := heven 
      omega 
    have h9 : ∃ k, (a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) = 2 * k := by
      refine' ⟨(a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) / 2, by 
        omega 
      ⟩ 
    exact h9 
  rcases h5 with ⟨k, hk⟩
  use (2 ^ k)
  have h10 : (2 ^ k) ^ 2 = 2 ^ (2 * k) := by 
    ring_nf 
  calc 
    (2 ^ k) ^ 2 = 2 ^ (2 * k) := h10 
    _ = 2 ^ ((a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) ) := by 
      rw [show 2 * k = (a * 1000 + b * 100 + 60 + 25 * (a * 10 + b)) by 
        omega 
      ]