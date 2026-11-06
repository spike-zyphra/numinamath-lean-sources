import Mathlib

theorem algebra_98474 :
    Set.ncard {a : ℝ | ∃ x, x^2 + a * x + 1 = 0 ∧ x^2 - x - a = 0} = 1 := by
  have h1 : {a : ℝ | ∃ x, x^2 + a * x + 1 = 0 ∧ x^2 - x - a = 0} = {2} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume there exists x such that both equations hold
      rintro ⟨x, h₁, h₂⟩
      have eq1 : x^2 + a * x + 1 = 0 := h₁
      have eq2 : x^2 - x - a = 0 := h₂
      have h3 : (x^2 + a * x + 1) - (x^2 - x - a) = 0 := by linarith
      have h4 : x * (a + 1) + (1 + a) = 0 := by
        nlinarith
      have h5 : (x + 1) * (a + 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case where x + 1 = 0, so x = -1
        have hx : x = -1 := by linarith
        rw [hx] at eq1 eq2
        nlinarith
      · -- Case where a + 1 = 0, so a = -1
        have ha : a = -1 := by linarith
        rw [ha] at eq1 eq2
        have h8 : x^2 - x + 1 = 0 := by nlinarith
        have h9 : x^2 - x + 1 > 0 := by
          nlinarith [sq_nonneg (x - 1 / 2)]
        linarith
    · -- Assume a = 2, show existence of x
      intro h1
      rw [h1]
      use -1
      constructor
      · -- Check first equation
        norm_num
      · -- Check second equation
        norm_num
  rw [h1]
  norm_num