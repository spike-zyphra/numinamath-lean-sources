import Mathlib

theorem algebra_11061 (a : ℝ) (f : ℕ → ℝ) (hf : ∀ x, f x = a * x ^ 2 + x)
    (h3 : f 3 < f 4) (h4 : ∀ n ≥ 8, f n > f (n + 1)) :
    a ∈ Set.Ioo (-1 / 7) (-1 / 17) := by
  have h31 : f 3 = a * 3^2 + 3 := hf 3
  have h32 : f 4 = a * 4^2 + 4 := hf 4
  rw [h31, h32] at h3
  have h33 : a > (-1 / 7 : ℝ) := by
    linarith
  have h41 : f 8 > f 9 := h4 8 (by norm_num)
  have h42 : f 8 = a * 8^2 + 8 := hf 8
  have h43 : f 9 = a * 9^2 + 9 := hf 9
  rw [h42, h43] at h41
  -- Simplify the inequality to get upper bound for a
  have h44 : a < (-1 / 17 : ℝ) := by
    norm_num at h41
    linarith
  -- Now we can conclude that a is in the open interval (-1/7, -1/17)
  exact ⟨h33, h44⟩