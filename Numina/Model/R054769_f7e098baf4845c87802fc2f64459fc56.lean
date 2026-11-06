import Mathlib

theorem number_theory_320433 (a : Fin 6 → ℤ) (ha : ∑ i, a i = 20) (ha' : ∀ i, a i > 0)
    (ha'' : ∀ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k → a i + a j ≤ a k) :
    False := by 
  have h1 := ha' 0
  have h2 := ha' 1
  have h3 := ha' 2
  have h4 := ha' 3
  have h5 := ha' 4
  have h6 := ha' 5
  have h7 : a 0 + a 1 ≤ a 2 := by
    specialize ha'' 0 1 2 (by simp)
    simpa using ha''
  have h8 : a 0 + a 2 ≤ a 1 := by
    specialize ha'' 0 2 1 (by simp)
    simpa using ha''
  omega