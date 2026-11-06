import Mathlib

theorem number_theory_322332 (x y z : ℤ) :
    4 * x + 7 * y + 14 * z = 40 ↔ ∃ u t : ℤ, x = 10 - 7 * u + 7 * t ∧ y = 2 * t ∧ z = 2 * u - 3 * t := by
  constructor
  · -- Assume 4 * x + 7 * y + 14 * z = 40, prove the existence of u and t
    intro h
    have h1 : y % 2 = 0 := by
      omega
    have h2 : ∃ t : ℤ, y = 2 * t := by
      refine' ⟨y / 2, by omega⟩
    rcases h2 with ⟨t, ht⟩
    have h3 : (y + 2 * z) % 4 = 0 := by
      omega
    have h4 : ∃ k : ℤ, y + 2 * z = 4 * k := by 
      refine' ⟨(y + 2 * z) / 4, by omega⟩
    rcases h4 with ⟨k, hk⟩
    have hx : x = 10 - 7 * k := by 
      omega
    have h5 : (z + 3 * t) % 2 = 0 := by 
      omega
    have h6 : ∃ u : ℤ, z + 3 * t = 2 * u := by 
      refine' ⟨(z + 3 * t) / 2, by omega⟩
    rcases h6 with ⟨u, hu⟩
    exact ⟨u, t, by omega⟩
  · -- Assume the existence of u and t, prove 4 * x + 7 * y + 14 * z = 40
    rintro ⟨u, t, hx, hy, hz⟩
    omega