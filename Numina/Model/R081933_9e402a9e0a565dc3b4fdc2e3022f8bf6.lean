import Mathlib

theorem algebra_136106 {a b : ℝ} (h : a^2 / (1 + a^2) + b^2 / (1 + b^2) = 1) :
    (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 0 ∨ (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 2 := by

  have h1 : a^2 * (1 + b^2) = 1 + a^2 := by
    have ha : 1 + a^2 ≠ 0 := by
      positivity
    have hb : 1 + b^2 ≠ 0 := by
      positivity
    field_simp at h ⊢
    nlinarith

  have h2 : a^2 * b^2 = 1 := by
    nlinarith

  have h3 : a * b = 1 ∨ a * b = -1 := by
    have h4 : (a * b) ^ 2 = 1 := by
      nlinarith
    cases' (sq_eq_one_iff.mp h4) with h5 h6
    · left
      linarith
    · right
      linarith

  cases' h3 with hab1 hab2

  · -- Case $ab = 1$
    have h1p : (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 2 ∨ (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 0 := by
      have ha : 1 + a^2 ≠ 0 := by positivity
      have hb : 1 + b^2 ≠ 0 := by positivity

      have eq1 : a / (1 + a^2) + b / (1 + b^2) = 2 * (a + b) / ((1 + a^2) * (1 + b^2)) := by
        have h4 : a * b = 1 := hab1
        field_simp
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

      have eq2 : (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = (a + b) * (2 * (a + b) / ((1 + a^2) * (1 + b^2))) := by
        rw [eq1]

      have eq3 : (1 + a^2) * (1 + b^2) = (a + b) ^ 2 := by
        have h4 : a * b = 1 := hab1
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

      rw [eq3] at eq2

      by_cases h5 : a + b = 0
      · -- Let's prove that it's 0
        have eq4 : (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 0 := by
          rw [eq2]
          simp [h5]
        right
        linarith
      · -- a + b ≠ 0
        have eq5 : (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 2 := by
          rw [eq2]
          have h5' : (a + b) ≠ 0 := h5
          field_simp [h5']
          <;> nlinarith
        left
        linarith

    cases' h1p with h1p1 h1p2
    · right
      linarith
    · left
      linarith

  · -- Case $ab = -1$
    have h2p : (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 0 := by
      have ha : 1 + a^2 ≠ 0 := by positivity
      have hb : 1 + b^2 ≠ 0 := by positivity

      have eq1 : a / (1 + a^2) + b / (1 + b^2) = 0 := by
        have h4 : a * b = -1 := hab2
        field_simp
        nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

      have eq2 : (a + b) * (a / (1 + a^2) + b / (1 + b^2)) = 0 := by
        rw [eq1]
        ring

      linarith

    left
    linarith