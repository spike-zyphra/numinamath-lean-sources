import Mathlib

theorem algebra_291533 {a b c: ℝ} (h: |a| = b ^ 2 * (b - c))
(l: (a = 0 ∧ 0 < b ∧ c < 0) ∨ (a = 0 ∧ 0 < c ∧ b < 0) ∨
(b = 0 ∧ 0 < a ∧ c < 0) ∨ (b = 0 ∧ 0 < c ∧ a < 0) ∨
(c = 0 ∧ 0 < a ∧ b < 0) ∨ (c = 0 ∧ 0 < b ∧ a < 0)): c = 0 ∧ 0 < b ∧ a < 0 := by
  rcases l with l | l | l | l | l | l
  · -- Case (a = 0 ∧ 0 < b ∧ c < 0)
    rcases l with ⟨l1, l2, l3⟩
    have h1 : a = 0 := l1
    have h2 : 0 < b := l2
    have h3 : c < 0 := l3
    have eq1 : |a| = 0 := by
      rw [h1]
      norm_num
    have eq2 : b ^ 2 * (b - c) = 0 := by 
      linarith [h, eq1]
    have eq3 : b^2 > 0 := by 
      nlinarith 
    have eq4 : b - c = 0 := by 
      nlinarith 
    have eq5 : c = b := by linarith 
    nlinarith 
  · -- Case (a = 0 ∧ 0 < c ∧ b < 0)
    rcases l with ⟨l1, l2, l3⟩
    have h1 : a = 0 := l1
    have h2 : 0 < c := l2
    have h3 : b < 0 := l3
    have eq1 : |a| = 0 := by
      rw [h1]
      norm_num
    have eq2 : b ^ 2 * (b - c) = 0 := by 
      linarith [h, eq1]
    have eq3 : b^2 > 0 := by 
      nlinarith 
    have eq4 : b - c = 0 := by 
      nlinarith 
    have eq5 : c = b := by linarith 
    have eq6 : c < 0 := by linarith 
    nlinarith 
  · -- Case (b = 0 ∧ 0 < a ∧ c < 0)
    rcases l with ⟨l1, l2, l3⟩
    have h1 : b = 0 := l1
    have h2 : 0 < a := l2
    have h3 : c < 0 := l3
    have eq1 : b = 0 := h1 
    have eq2 : |a| = 0 := by 
      rw [eq1] at h 
      nlinarith 
    have eq3 : a = 0 := by 
      simpa [abs_eq_zero] using eq2 
    nlinarith 
  · -- Case (b = 0 ∧ 0 < c ∧ a < 0)
    rcases l with ⟨l1, l2, l3⟩
    have h1 : b = 0 := l1
    have h2 : 0 < c := l2
    have h3 : a < 0 := l3
    have eq1 : b = 0 := h1 
    have eq2 : |a| = 0 := by 
      rw [eq1] at h 
      nlinarith 
    have eq3 : a = 0 := by 
      simpa [abs_eq_zero] using eq2 
    nlinarith 
  · -- Case (c = 0 ∧ 0 < a ∧ b < 0)
    rcases l with ⟨l1, l2, l3⟩
    have h1 : c = 0 := l1
    have h2 : 0 < a := l2
    have h3 : b < 0 := l3
    rw [h1] at h 
    -- Now |a| = b^2 * b
    have eq1 : |a| = a := abs_of_pos (show (0 : ℝ) < a by linarith)
    have eq4 : a = b^3 := by 
      nlinarith [sq_nonneg (b)]
    nlinarith [sq_nonneg (b), sq_nonneg (a - 0)]
  · -- Case (c = 0 ∧ 0 < b ∧ a < 0)
    rcases l with ⟨l1, l2, l3⟩
    exact ⟨l1, l2, l3⟩