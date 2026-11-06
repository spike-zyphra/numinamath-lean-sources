import Mathlib


lemma lemma_1 (x y z V : ℕ) (h : x + y + z = 50) (h' : x*1+y*2+z*5=V) :
    y+4*z=V-50 := by
  have eq4 : x + 2 * y + 5 * z = V := by
    linarith
  have eq5 : 50 + (y : ℕ) + 4 * z = V := by
    have h6 : x = 50 - y - z := by
      omega
    rw [h6] at eq4
    omega
  have h4 : V ≥ 50 := by
    omega
  omega


theorem algebra_6036 (x y z : ℕ) (h : x + y + z = 50) (h' : x*1+y*2+z*5=100) :
    ∃ t : ℤ, x=36+3*t ∧ y=2-4*t ∧ z=12+t ∧ t ∈ Finset.Icc (-12) 0 := by
  have h1 : y + 4 * z = 50 := by
    have h2 : x + y + z = 50 := by
      exact h
    have h3 : x * 1 + y * 2 + z * 5 = 100 := by
      exact_mod_cast h'
    omega
  have h2 : x =3 * z := by
    omega
  use ((z : ℤ) - 12)
  constructor
  · -- Show x = 36 + 3 * t
    omega
  constructor
  · -- Show y = 2 -4 * t
    omega
  constructor
  · -- Show z = 12 + t
    omega
  · -- Show t ∈ Finset.Icc (-12) 0
    have h4 : z ≤ 12 := by
      omega
    have h5 : z ≥ 0 := by
      omega
    simp [Finset.mem_Icc]
    all_goals omega