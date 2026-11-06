import Mathlib

theorem number_theory_159564 (n : ℤ) : Even (n * (n + 1)) := by
  have h1 : n % 2 = 0 ∨ n % 2 = 1 := by 
    omega
  rcases h1 with (h | h)
  · -- Assume n % 2 = 0
    have h2 : n % 2 = 0 := h
    have h3 : (n * (n + 1)) % 2 = 0 := by
      simp [Int.mul_emod, Int.add_emod, h2]
    exact ⟨(n * (n + 1)) / 2, by omega⟩
  · -- Assume n % 2 = 1
    have h4 : n % 2 = 1 := h
    have h5 : (n + 1) % 2 = 0 := by 
      omega
    have h6 : (n * (n + 1)) % 2 = 0 := by
      simp [Int.mul_emod, h5]
    exact ⟨(n * (n + 1)) / 2, by omega⟩