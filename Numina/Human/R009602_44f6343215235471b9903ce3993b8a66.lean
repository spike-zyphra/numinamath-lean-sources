import Mathlib

theorem algebra_359209 {f : ℝ → ℝ} (hf : ∀ x, x ≠ -1/3 → x ≠ a → f x = x / ((3 * x + 1) * (x - a)))
    (hodd : ∀ x, f (-x) = -f x) : a = 1 / 3 := by
    have ane1 : a ≠ 1 := by
      intro h; simp [h] at hf
      have := hf 2 (by linarith) (by linarith)
      norm_num at this
      have := hf (-2) (by linarith) (by linarith)
      norm_num at this
      specialize hodd 2; linarith
    have anem1 : a ≠ -1 := by
      intro h; simp [h] at hf
      have := hf 2 (by linarith) (by linarith)
      norm_num at this
      have := hf (-2) (by linarith) (by linarith)
      norm_num at this
      specialize hodd 2; linarith
    have h1 := hf 1 (by linarith) (by symm; exact ane1)
    have hm1 := hf (-1) (by linarith) (by symm; exact anem1)
    symm at ane1 anem1; rw [← sub_ne_zero] at ane1 anem1
    specialize hodd 1; rw [h1, hm1] at hodd
    field_simp at hodd; linarith