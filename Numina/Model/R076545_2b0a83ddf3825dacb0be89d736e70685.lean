import Mathlib

theorem algebra_235238 {f : ℝ → ℝ} (hf : ∀ x > 0, f x > 0)
    (h : ∀ A B : ℝ, A > 0 → B > 0 → A * B = (A + B) * (f A + f B) / 2) :
    f 1 = 4 → f 4 = 1 := by
  intro h1
  have h11 := h 1 1 (by norm_num) (by norm_num)
  norm_num [h1] at h11
  all_goals linarith [hf 1 (by norm_num), hf 1 (by norm_num)]