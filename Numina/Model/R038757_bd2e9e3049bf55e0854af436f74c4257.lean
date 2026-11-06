import Mathlib

theorem algebra_317576 (a : ℕ → ℤ) (ha : Monotone a)
    (ha1 : ∀ n, 0 < a n) (h : ∀ n, a (n + 2) = 3 * a (n + 1) - a n)
    (h6 : a 6 = 280) : a 7 = 733 := by 
  have h1 : a 0 ≤ a 1 := by apply ha; all_goals simp
  have h2 : a 1 ≤ a 2 := by apply ha; all_goals simp
  have h3 : a 2 ≤ a 3 := by apply ha; all_goals simp
  have h4 : a 3 ≤ a 4 := by apply ha; all_goals simp
  have h5 : a 4 ≤ a 5 := by apply ha; all_goals simp
  have h6' : a 5 ≤ a 6 := by apply ha; all_goals simp
  have h7' : a 6 ≤ a 7 := by apply ha; all_goals simp
  have h8' : a 7 ≤ a 8 := by apply ha; all_goals simp
  have h9' : a 8 ≤ a 9 := by apply ha; all_goals simp

  have h7 : a 2 = 3 * a 1 - a 0 := by
    specialize h 0
    simpa using h

  have h8 : a 3 = 3 * a 2 - a 1 := by
    specialize h 1
    simpa using h

  have h9 : a 4 = 3 * a 3 - a 2 := by
    specialize h 2
    simpa using h

  have h10 : a 5 = 3 * a 4 - a 3 := by
    specialize h 3
    simpa using h

  have h11 : a 6 = 3 * a 5 - a 4 := by
    specialize h 4
    simpa using h

  have h12 : a 7 = 3 * a 6 - a 5 := by
    specialize h 5
    simpa using h

  have h13 : a 8 = 3 * a 7 - a 6 := by
    specialize h 6
    simpa using h

  have h14 : a 9 = 3 * a 8 - a 7 := by
    specialize h 7
    simpa using h

  have a0 : 0 < a 0 := ha1 0
  have a1 : 0 < a 1 := ha1 1
  have a2 : 0 < a 2 := ha1 2
  have a3 : 0 < a 3 := ha1 3
  have a4 : 0 < a 4 := ha1 4
  have a5 : 0 < a 5 := ha1 5
  have a6 : 0 < a 6 := ha1 6
  have a7 : 0 < a 7 := ha1 7
  have a8 : 0 < a 8 := ha1 8
  have a9 : 0 < a 9 := ha1 9 
  omega