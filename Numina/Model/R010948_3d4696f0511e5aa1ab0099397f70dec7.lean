import Mathlib

theorem number_theory_4633 (n d q : ℕ) (h1 : n + d + q = 24)
    (h2 : 5*n+10*d+25*q=200) :
    (n=8∧d=16∧q=0) ∨ (n=11∧d=12∧q=1) ∨ (n=14∧d=8∧q=2) ∨
    (n=17∧d=4∧q=3) ∨ (n=20∧d=0∧q=4):= by

  have eq1 : n + 2 * d + 5 * q = 40 := by 
    omega

  have eq2 : d + 4 * q = 16 := by
    omega

  have h3 : q ≤ 4 := by 
    omega

  have : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 := by
    omega

  rcases this with (h | h | h | h | h)
  · -- q = 0
    have h4 : q = 0 := h
    have h5 : d = 16 := by 
      omega
    have h6 : n = 8 := by
      omega
    left 
    constructor 
    · exact h6
    constructor 
    · exact h5
    · exact h4

  · -- q = 1
    have h4 : q = 1 := h
    have h5 : d = 12 := by 
      omega
    have h6 : n = 11 := by 
      omega 
    right 
    left 
    constructor 
    · exact h6
    constructor 
    · exact h5
    · exact h4

  · -- q = 2
    have h4 : q = 2 := h 
    have h5 : d = 8 := by 
      omega
    have h6 : n = 14 := by
      omega 
    right 
    right 
    left 
    constructor 
    · exact h6
    constructor 
    · exact h5
    · exact h4

  · -- q = 3
    have h4 : q = 3 := h
    have h5 : d = 4 := by 
      omega
    have h6 : n = 17 := by
      omega 
    right 
    right 
    right 
    left 
    constructor 
    · exact h6
    constructor 
    · exact h5
    · exact h4

  · -- q = 4 
    have h4 : q = 4 := h 
    have h5 : d = 0 := by 
      omega
    have h6 : n = 20 := by
      omega 
    right 
    right 
    right 
    right 
    constructor 
    · exact h6 
    constructor 
    · exact h5 
    · exact h4