import Mathlib

theorem number_theory_105516 (a : ℕ → ℕ) (ha : a 0 = 1)
    (h : ∀ n, a (n + 1) = if a n < 10 then 2 * a n else a n + 5)
    (h' : a 99 = 5) :
    a 98 = 8 := by 
  have eq1 : a 99 = if a 98 < 10 then 2 * a 98 else a 98 + 5 := by 
    specialize h 98 
    norm_num at h ⊢
    simpa using h 
  rw [h'] at eq1 
  by_cases h1 : a 98 < 10 
  · -- case where a 98 < 10, so eq1 becomes 5 = 2 * a 98
    simp [h1] at eq1 
    exfalso 
    have h0 : a 98 ≤ 4 := by 
      omega 
    interval_cases a 98 <;> simp at eq1 <;> linarith 
  · -- case where a 98 ≥ 10, so eq1 becomes 5 = a 98 + 5
    have h2 : a 98 ≥ 10 := by 
      omega 
    simp [show ¬(a 98 < 10) by omega] at eq1 
    exfalso 
    have eq3 : a 98 + 5 = 5 := by
      linarith [eq1]
    have eq4 : a 98 = 0 := by 
      omega 
    linarith [eq4, h2]