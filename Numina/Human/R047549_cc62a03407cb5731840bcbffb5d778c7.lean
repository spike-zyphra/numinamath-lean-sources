import Mathlib
open Real Set

/- Let $x$ be a real number such that $0 < x < \frac{\pi}{2}$. Prove that
$$\cos ^{2}(x) \cot (x)+\sin ^{2}(x) \tan (x) \geq 1 \text {.}$$-/

theorem inequality_606436 (x : ℝ) (xs : x ∈ Ioo 0 (Real.pi / 2)):
(cos x) ^ 2 * cot x + (sin x) ^ 2 * tan x ≥ 1 := by
  -- show that sinx and cosx greater than 0
  have sin_pos : sin x > 0 := by
    apply sin_pos_of_mem_Ioo
    simp at *
    exact ⟨by linarith, by linarith⟩
  have cos_pos : cos x > 0 := by
    apply cos_pos_of_mem_Ioo
    simp at *
    exact ⟨by linarith, by linarith⟩
  -- rewrite cot and tan with sin and cos
  rw [cot_eq_cos_div_sin, tan_eq_sin_div_cos]

  -- show that cos x * sin x ≤ 1 / 2
  have h1 : cos x * sin x ≤ 1 / 2 := by
    calc 
      _ = - (cos x - sin x) ^ 2 / 2 + (cos x ^ 2 + sin x ^ 2) / 2 := by ring
      _ ≤ (cos x ^ 2 + sin x ^ 2) / 2 := by linarith [sq_nonneg (cos x - sin x)]
      _ = 1 / 2 := by simp
  -- show that cos x ^ 4 + sin x ^ 4 ≥ 1 / 2
  have h2 : cos x ^ 4 + sin x ^ 4 ≥ 1 / 2 := by
    calc _ = (cos x ^ 2 + sin x ^ 2) ^ 2 - 2 * (cos x * sin x) ^ 2 := by ring
      _ = 1 - 2 * (cos x * sin x) ^ 2 := by simp
      _ ≥ 1 - 2 * (1 / 2) ^ 2 := by
        have : (cos x * sin x) ^ 2 ≤ (1 / 2) ^ 2  := by
          apply sq_le_sq'
          linarith [mul_pos sin_pos cos_pos]
          exact h1
        linarith [this]
      _ = 1 / 2 := by norm_num

  -- finish the theorem
  calc
    _ = (cos x ^ 4 + sin x ^ 4) / (cos x * sin x) := by field_simp; ring
    _ ≥ (1 / 2) / (1 / 2) := by
      apply div_le_div
      positivity
      exact h2
      positivity
      exact h1
    _ = 1 := by norm_num
