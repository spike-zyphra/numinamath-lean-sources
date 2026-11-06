import Mathlib

theorem algebra_2566 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : (1 / a) / (1 / b) = 2 / 3 ∧ (1 / b) / (1 / c) = 3 / 4) :
    a / b = 6 / 4 ∧ b / c = 4 / 3 := by
  rcases h with ⟨h1, h2⟩
  have h3 : (1 / a) / (1 / b) = b / a := by
    field_simp [ha, hb]
    all_goals linarith
  rw [h3] at h1
  have h4 : (1 / b) / (1 / c) = c / b := by 
    field_simp [hb, hc]
    all_goals linarith
  rw [h4] at h2

  constructor
  · -- Prove $a/b = 6/4$
    field_simp [ha, hb] at h1 ⊢
    linarith
  · -- Prove $b/c = 4/3$
    field_simp [hb, hc] at h2 ⊢
    linarith