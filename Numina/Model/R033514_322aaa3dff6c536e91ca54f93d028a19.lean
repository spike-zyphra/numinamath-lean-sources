import Mathlib

theorem algebra_9018 {f : ℝ → ℝ}{a:ℝ}(hf : f = fun x => 3 * x ^ (a - 2) - 2) (ha : f 2 = 4) : a = 3 := by
rw [hf] at ha
simp at ha

have h1: (2:ℝ)^(a-2:ℝ) = 2 := by
  have ht1:  3 * 2 ^ (a - 2:ℝ) = (6:ℝ) := by
    have: 6 = (4:ℝ) + 2 := by norm_num
    rw [this]
    rw [← ha]
    ring
  have ht3: (2:ℝ) ^ (a - 2:ℝ) = (6:ℝ) / 3 := by
    have ht4: (2:ℝ) ^ (a - 2:ℝ) = (6:ℝ) / 3 := by
      field_simp
      linarith
    linarith
  norm_num at ht3 ⊢
  linarith

have h2: a - 2 = (1:ℝ) := by
  have h3: (2:ℝ)^(a - 2:ℝ) = (2:ℝ)^(1:ℝ) := by
    rw [h1]
    norm_num
  have ht1: a - 2 = (1:ℝ) := by
    apply_fun (Real.logb 2) at h3
    have ht2: Real.logb 2 ((2:ℝ)^(a-2:ℝ)) = Real.logb 2 ((2:ℝ)^(1:ℝ)) := h3
    have ht3: Real.logb 2 ((2:ℝ)^(a-2:ℝ)) = (a-2:ℝ) := (Real.logb_rpow (by norm_num) (by norm_num))
    have ht4: Real.logb 2 ((2:ℝ)^(1:ℝ)) = (1:ℝ) := by
      simp [Real.logb_pow]
    rw [ht3, ht4] at ht2
    linarith
  linarith

linarith