import Mathlib

theorem algebra_213096 :
  let a : Fin 100 → Fin 100 → ℤ := fun i j => 
    if j = 0 then 1 else 1 + (j : ℕ) * ((i : ℕ) + 1) 
  IsGreatest {x | ∃ i : Fin 100, a i (99 - i) = x} 2501 := by 
  intro a 
  constructor
  · -- Show that 2501 is in the set 
    use 49
    native_decide 
  · -- Show that 2501 is greatest in the set 
    intro x hx
    rcases hx with ⟨i, hi⟩
    simp [a] at hi 
    by_cases h_zero : (99 - i : Fin 100) = (0 : Fin 100)
    · -- Case where 99 - i = 0. Then i = 99.
      have h1 : (i : ℕ) = 99 := by 
        simp [Fin.ext_iff] at h_zero ⊢ 
        omega 
      have hx1 : x = 1 := by 
        simp [h1] at hi 
        omega 
      omega 
    · -- Case where 99 - i ≠ 0 
      have h1 : (i : ℕ) ≤ 99 := by 
        simp at *
        all_goals 
          omega 
      have h4 : (1 + ↑↑(99 - i) * (↑↑i + 1) : ℤ) ≤ (2501 : ℤ) := by
        have h6 : (i : ℕ) ≤ 99 := h1 
        have h7 : (i : ℕ) < 100 := by 
          omega 
        have h8 : (1 + ↑↑(99 - i) * (↑↑i + 1) : ℤ) ≤ (2501 : ℤ) := by
          fin_cases i <;> simp at *
          all_goals omega 
        omega 
      omega