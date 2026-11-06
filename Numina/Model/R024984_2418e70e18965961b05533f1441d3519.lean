import Mathlib

theorem algebra_179341 {b c d : ℝ} (P Q : ℝ → ℝ)
    (hP : P = fun x => x^2 + x / 2 + b) (hQ : Q = fun x => x^2 + c * x + d)
    (h : ∀ x, P x * Q x = Q (P x)) :
    {x | P (Q x) = 0} = {-1, 1 / 2} := by
  have eq1 := h 0
  simp [hP, hQ] at eq1
  have eq2 := h 1
  simp [hP, hQ] at eq2
  have eq3 := h 2
  simp [hP, hQ] at eq3
  have eq4 := h 3
  simp [hP, hQ] at eq4
  have eq5 := h 4
  simp [hP, hQ] at eq5
  have hc : c = 1 / 2 := by
    nlinarith
  have hb : b = -1 / 2 := by
    rw [hc] at eq2 eq3 eq4 eq5
    nlinarith
  have hd : d = 0 := by
    rw [hc, hb] at eq1
    nlinarith
  have hP1 : P = fun x => x^2 + x / 2 - 1 / 2 := by
    rw [hP]
    funext
    rw [hb]
    all_goals ring
  have hQ1 : Q = fun x => x^2 + (1 / 2) * x := by 
    rw [hQ]
    funext
    rw [hc, hd]
    all_goals ring
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  simp [hP1, hQ1]
  constructor
  · -- Assume P (Q x) = 0, prove x = -1 ∨ x = 1/2 
    intro h_eq
    have h_eq2 : (x^2 + (1 / 2) * x - 1 / 2) * (x^2 + (1 / 2) * x + 1) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h_eq2) with h_eq3 h_eq4
    · -- Case where x^2 + (1/2)x - 1/2 = 0
      have h_eq5 : (x + 1) * (x - 1 / 2) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.1 h_eq5) with h_eq6 h_eq7
      · -- Case x + 1 = 0, so x = -1 
        left
        linarith 
      · -- Case x - 1/2 = 0, so x = 1/2 
        right
        linarith 
    · -- Case where x^2 + (1/2)x + 1 = 0 
      nlinarith [sq_nonneg (x + 1 / 4)]
  · -- Assume x = -1 ∨ x = 1/2, prove P (Q x) = 0 
    rintro (h_eq | h_eq)
    · -- Case x = -1 
      rw [h_eq]
      norm_num
    · -- Case x = 1/2 
      rw [h_eq]
      norm_num