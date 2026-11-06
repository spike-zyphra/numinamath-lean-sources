import Mathlib

theorem algebra_21985 {a b c : ℝ} (star : ℝ → ℝ → ℝ)
    (hstar : star = λ x y ↦ a * x + b * x + c * x * y)
    (h₁ : star 1 2 = 3) (h₂ : star 2 3 = 4) : 
    {d |d ≠ 0 ∧ ∀ x, star x d = x } = {4}:= by
  ext d 
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor 
  · -- first, prove that if d is in the left side, then d = 4
    intro h 
    rcases h with ⟨hd, h_eq⟩
    have eq1 : a * 1 + b * 1 + c * 1 * d = 1 := by
      specialize h_eq 1
      simp [hstar] at h_eq ⊢
      linarith
    have eq2 : a * 2 + b * 2 + c * 2 * d = 2 := by 
      specialize h_eq 2 
      simp [hstar] at h_eq ⊢
      linarith
    have eq3 : a * 1 + b * 1 + c * 1 * 2 = 3 := by
      simp [hstar] at h₁ ⊢
      linarith
    have eq4 : a * 2 + b * 2 + c * 2 * 3 = 4 := by
      simp [hstar] at h₂ ⊢ 
      linarith
    have eq5 : c = -1 := by
      nlinarith
    have eq6 : a + b = 5 := by 
      nlinarith [eq3, eq4, eq5]
    have eq7 : a + b + c * d = 1 := by
      linarith [eq1]
    have hd' : d = 4 := by
      rw [show c = -1 by linarith] at eq7
      nlinarith [eq6, eq7]
    linarith 
  · -- now the reverse. If d = 4, then it's in the left side.
    intro h_eq 
    constructor 
    · -- prove d ≠0
      rw [h_eq] 
      norm_num 
    · -- prove for all x, star x d = x 
      intro x 
      have eq7 : a * x + b * x + c * x * 4 = x := by 
        have eq7 : c = -1 := by 
          have eq1 : a * 1 + b * 1 + c * 1 * 2 = 3 := by 
            simp [hstar] at h₁ ⊢ 
            linarith 
          have eq2 : a * 2 + b * 2 + c * 2 * 3 = 4 := by
            simp [hstar] at h₂ ⊢ 
            linarith 
          nlinarith 
        have eq8 : a + b = 5 := by 
          have eq1 : a * 1 + b * 1 + c * 1 * 2 = 3 := by 
            simp [hstar] at h₁ ⊢ 
            linarith 
          have eq2 : a * 2 + b * 2 + c * 2 * 3 = 4 := by
            simp [hstar] at h₂ ⊢ 
            linarith 
          nlinarith [eq1, eq2, eq7]
        have eq9 : a * x + b * x + c * x * 4 = x := by 
          rw [eq7] 
          have eq10 : a * x + b * x + (-1) * x * 4 = (a + b - 4) * x := by 
            ring 
          rw [eq10] 
          have eq11 : a + b - 4 = 1 := by 
            linarith [eq8] 
          rw [eq11] 
          all_goals linarith 
        linarith 
      simp [hstar, h_eq] at *
      all_goals try { 
        linarith [eq7] 
      }