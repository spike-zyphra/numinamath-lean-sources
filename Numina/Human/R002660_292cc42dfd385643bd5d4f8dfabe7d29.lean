import Mathlib

theorem algebra_98101 {a b : ℝ}
  (h₀ : Real.sin a + Real.sin b = Real.sqrt (5 / 3))
  (h₁ : Real.cos a + Real.cos b = 1)
  : Real.cos (a - b) = 1 / 3 := by

  set sin_a := Real.sin a
  set sin_b := Real.sin b
  set cos_a := Real.cos a
  set cos_b := Real.cos b

  have h_mod : 2 * Real.cos (a - b) = 2 / 3 ↔ Real.cos (a - b) = 1 / 3 := by
    constructor <;>
    · intro h
      linarith

  apply h_mod.mp

  have hPytagora_sin:  sin_a ^ 2 + sin_b ^2 + 2 * sin_a * sin_b = 5/3 := by
    calc
     sin_a ^ 2 + sin_b ^2 + 2 * sin_a * sin_b = (sin_a + sin_b) * (sin_a + sin_b) := by ring
     _ = Real.sqrt (5 / 3) * Real.sqrt (5 / 3) := by rw [h₀]
     _ = Real.sqrt (5 / 3) ^2 := by exact Eq.symm (pow_two √(5 / 3))
     _ = 5/3 := Real.sq_sqrt (by norm_num)

  have hPytahora_cos: cos_a^2 + cos_b^2 + 2 * cos_a * cos_b = 1 := by
    calc
      cos_a^2 + cos_b^2 + 2 * cos_a * cos_b  = (cos_a + cos_b) * (cos_a + cos_b) := by ring
      _ = 1 * 1 := by rw [h₁]
      _ = 1 := by ring
  
  have h2_sin_sin: 2 * sin_a * sin_b = 5/3 - sin_a^2 - sin_b^2 := by linarith
  have h2_cos_cos: 2 * cos_a * cos_b = 1 - cos_a^2 - cos_b^2 := by linarith


  rw [Real.cos_sub]; ring_nf

  calc
    cos_a * cos_b * 2 + sin_a * sin_b * 2 = 2*cos_a * cos_b + 2*sin_a * sin_b := by ring
    _ = 1 - cos_a^2 - cos_b^2 + (5/3 - sin_a^2 - sin_b^2) := by rw [h2_cos_cos, h2_sin_sin]
    _ = 1 - cos_a^2 - cos_b^2 + 5/3 - sin_a^2 - sin_b^2 := by linarith
    _ = 1 + 5/3 - cos_a^2 - cos_b^2 - sin_a^2 - sin_b^2 := by ring
    _ = 8/3 - cos_a^2 - cos_b^2 - sin_a^2 - sin_b^2 := by ring
    _ = 8/3 - sin_a^2 - cos_a^2 - sin_b^2 - cos_b^2 := by ring
    _ = 8/3 - (sin_a^2 + cos_a^2) - (sin_b^2 + cos_b^2) := by ring
    _ = 8/3 - 1 - 1 := by rw [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]
    _ = 2/3 := by norm_num