import Mathlib

theorem algebra_8544 (A B C D E : ℝ × ℝ) (h₀ : B - A = C - B) (h₁ : C - B = D - C)
    (h₂ : E - A • E - B = 4) (h₃ : E - B • E - C = 5) (h₄ : E - C • E - D = 8) :
    E - A • E - D = 3 := by
  have eq1 : C.1 = 2 * B.1 - A.1 := by
    have eq1 : (B.1 - A.1) = (C.1 - B.1) := by 
      simpa using congr_arg Prod.fst h₀
    linarith
  have eq2 : C.2 = 2 * B.2 - A.2 := by
    have eq2 : (B.2 - A.2) = (C.2 - B.2) := by 
      simpa using congr_arg Prod.snd h₀
    linarith
  have eq3 : D.1 = 2 * C.1 - B.1 := by
    have eq3 : (C.1 - B.1) = (D.1 - C.1) := by 
      simpa using congr_arg Prod.fst h₁
    linarith
  have eq4 : D.2 = 2 * C.2 - B.2 := by
    have eq4 : (C.2 - B.2) = (D.2 - C.2) := by 
      simpa using congr_arg Prod.snd h₁
    linarith
  have eq5 : D.1 = 3 * B.1 - 2 * A.1 := by
    rw [eq3]
    rw [eq1]
    linarith
  have eq6 : D.2 = 3 * B.2 - 2 * A.2 := by
    rw [eq4]
    rw [eq2]
    linarith
  simp [Prod.ext_iff, sub_eq_zero, eq1, eq2, eq5, eq6] at h₂ h₃ h₄ ⊢
  <;> ring_nf at h₂ h₃ h₄ ⊢
  <;> nlinarith