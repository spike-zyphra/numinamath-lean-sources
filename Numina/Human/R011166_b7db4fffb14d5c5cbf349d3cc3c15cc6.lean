import Mathlib

theorem algebra_611338 :
    {(a, b, c) : ℝ × ℝ × ℝ | a < b ∧ b < c ∧ a + b + c = 21 / 4 ∧ 1 / a + 1 / b + 1 / c = 21 / 4 ∧ a * b * c = 1} = {(1 / 4, 1, 4)} := by
  -- Simplify the goal into two parts.
  ext ⟨a, b, c⟩
  apply Iff.intro
  . -- First show that the system of equations implies the solution.
    simp [-one_div]
    intro h₀ h₁ h₂ h₃ h₄
    -- Show that a, b and c ≠ 0.
    have h₅ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 := by
      refine ⟨?_, ?_, ?_⟩
      all_goals
        by_contra!
        simp [this] at h₄
    -- Rewrite 1 / a + 1 / b + 1 / c = 21/4 to ab + bc + ca = 21/4.
    field_simp [h₅.1, h₅.2.1, h₅.2.2] at h₃
    rw [h₄] at h₃
    -- Note taht a, b and c are the roots of the polynomial (x - 1 / 4)(x - 1)(x - 4) by expanding and comparing coefficients.
    have h₆ (x : ℝ) : x ∈ ({a, b, c} : Set ℝ) → (x - 1 / 4) * (x - 1) * (x - 4) = 0 := by
      intro h
      simp at h
      -- Show that (x - 1 / 4)(x - 1)(x - 4) = (x - a)(x - b)(x - c) by expanding and comparing coefficients.
      have : (x - 1 / 4) * (x - 1) * (x - 4) = (x - a) * (x - b) * (x - c) := by
        ring_nf
        have g₀ := congr_arg (· * x ^ 2) h₂
        have g₁ := congr_arg (· * x) h₃
        simp only at g₀ g₁
        linarith
      rw [this]
      simp [sub_eq_zero]
      tauto
    -- Now the goal is trivial.
    simp [-one_div] at h₆
    obtain ⟨(ha | ha) | ha, (hb | hb) | hb, (hc | hc) | hc⟩ := h₆
    all_goals
      simp [sub_eq_zero, -one_div] at ha hb hc
      first | linarith | tauto
  . -- Now show that the solution satisfies the system of equations.
    simp [-one_div]
    intro ha hb hc
    subst ha hb hc
    norm_num
