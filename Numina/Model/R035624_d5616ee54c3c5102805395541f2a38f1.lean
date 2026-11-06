import Mathlib

theorem algebra_20136 (c : ℝ) :
    (∃! x, 3 * x ^ 2 + 4 * x + c = 0) ↔ c = 4 / 3 := by 
  constructor
  · -- Assume there exists a unique solution, prove c = 4/3
    intro h
    rcases h with ⟨x, ⟨h1, h2⟩⟩
    have h3 : 3 * x ^ 2 + 4 * x + c = 0 := h1
    have h4 : ∀ y, 3 * y ^ 2 + 4 * y + c = 0 → y = x := h2
    have h5 : - 4 / 3 - x = x := by
      have h6 : 3 * (- 4 / 3 - x) ^ 2 + 4 * (- 4 / 3 - x) + c = 0 := by
        nlinarith [h3]
      have h7 : - 4 / 3 - x = x := by
        apply h4 (- 4 / 3 - x) 
        all_goals 
          try nlinarith [h6, h3]
      linarith
    have h8 : x = - 2 / 3 := by 
      linarith 
    rw [h8] at h3
    nlinarith 
  · -- Assume c = 4/3, prove there exists a unique solution 
    intro h 
    rw [h]
    use -2 / 3 
    constructor 
    · -- Show that -2/3 is indeed a solution 
      norm_num 
    · -- Show that -2/3 is unique 
      intro y h_eq 
      have h_eq1 : 3 * y ^ 2 + 4 * y + 4 / 3 = 0 := by 
        linarith [h_eq] 
      have h_eq2 : 9 * y ^ 2 + 12 * y + 4 = 0 := by 
        linarith [h_eq1] 
      have h_eq3 : (3 * y + 2) ^ 2 = 0 := by 
        nlinarith [h_eq2] 
      have h_eq4 : 3 * y + 2 = 0 := by 
        nlinarith [h_eq3, sq_nonneg (3 * y + 2)]
      have h_eq5 : y = - 2 / 3 := by 
        linarith [h_eq4] 
      linarith