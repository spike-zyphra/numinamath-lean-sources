import Mathlib

theorem number_theory_79109 (x y : ℕ) :
    ∃ m n, (x + 1) / y = m ∧ (y + 1) / x = n ↔
    (x = 2 ∧ y = 1) ∨ (x = 3 ∧ y = 2) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) := by 
  by_cases h : (x = 2 ∧ y = 1) ∨ (x = 3 ∧ y = 2) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3)
  · -- Assume right side is true, so we have to prove the left side
    rcases h with (h | h | h | h)
    · -- Case where (x = 2 ∧ y = 1)
      have hx : x = 2 := h.1
      have hy : y = 1 := h.2
      use 3, 1
      simp [hx, hy]
    · -- Case where (x = 3 ∧ y = 2)
      have hx : x = 3 := h.1
      have hy : y = 2 := h.2
      use 2, 1
      simp [hx, hy]
    · -- Case where (x = 1 ∧ y = 2)
      have hx : x = 1 := h.1
      have hy : y = 2 := h.2
      use 1, 3
      simp [hx, hy]
    · -- Case where (x = 2 ∧ y = 3)
      have hx : x = 2 := h.1
      have hy : y = 3 := h.2
      use 1, 2
      simp [hx, hy]
  · -- Assume the right side is false, so we need the left side to be false
    have h' : ¬( (x = 2 ∧ y = 1) ∨ (x = 3 ∧ y = 2) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ) := by 
      simpa using h
    use (x + 1) / y + 1, (y + 1) / x + 1 
    constructor 
    · -- Assume the left side is true
      intro h1 
      exfalso 
      have h1' : (x + 1) / y = (x + 1) / y + 1 := by
        omega 
      omega 
    · -- Assume the right side is true
      intro h1 
      exfalso 
      tauto