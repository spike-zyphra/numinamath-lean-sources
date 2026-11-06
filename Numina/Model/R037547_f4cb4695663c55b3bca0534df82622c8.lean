import Mathlib

theorem number_theory_280259 (n : ℕ) :
    {a : ℕ | ∃ k : ℕ, n^6 + 3 * a = k ∧ k > 0}.Infinite := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (t : ℕ) => if n = 0 then t + 1 else t)
  · -- Show f is injective 
    by_cases h : n = 0
    · -- Case n = 0
      intro t s ht
      simp [h] at ht
      omega
    · -- Case n ≠ 0
      intro t s ht 
      simp [h] at ht 
      exact ht
  · -- Show all elements from the image of f are in the required set 
    intro t
    by_cases h : n = 0 
    · -- Case n = 0
      have hn0 : n = 0 := h
      have ha : (if n = 0 then t + 1 else t) = t + 1 := by 
        simp [hn0]
      use 3 * (t + 1)
      constructor
      · -- Show n^6 + 3 * (t + 1) = 3 * (t + 1) 
        simp [ha, hn0]
      · -- Show 3 * (t + 1) > 0 
        omega
    · -- Case n ≠ 0 
      have hn1 : n ≠ 0 := by 
        simpa using h
      have ha : (if n = 0 then t + 1 else t) = t := by 
        simp [show n ≠ 0 by simpa using h]
      use n^6 + 3 * t 
      constructor 
      · -- Show n^6 + 3 * a = k 
        simp [ha]
      · -- Show k > 0 
        have hn1' : n >= 1 := by 
          by_contra h1 
          push_neg at h1 
          have : n = 0 := by 
            omega 
          tauto 
        have h2 : n^6 > 0 := by 
          apply Nat.pow_pos 
          omega 
        omega