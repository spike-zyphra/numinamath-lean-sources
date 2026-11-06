import Mathlib

theorem number_theory_307696 (m n : ℤ) (h : Even (m^2 + n^2)) :
    ¬(Odd (m + n)) := by
  by_contra h1
  have h2 : m % 2 = 0 ∨ m % 2 = 1 := by omega
  have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have h4 : (m + n) % 2 = 1 := by 
    obtain ⟨k, hk⟩ := h1
    omega
  have h5 : (m ^ 2 + n ^ 2) % 2 = 0 := by
    have h6 : Even (m^2 + n^2) := h
    obtain ⟨k, hk⟩ := h6
    omega
  rcases h2 with (h2 | h2) <;> rcases h3 with (h3 | h3) <;> simp [pow_two, Int.add_emod, Int.mul_emod, h2, h3] at h4 h5 <;> omega