import Mathlib
open Real

/-
When a right triangle is rotated about one leg, the volume of the cone produced is $800\pi \;\textrm{ cm}^3$. When the triangle is rotated about the other leg, the volume of the cone produced is $1920\pi \;\textrm{ cm}^3$. What is the length (in cm) of the hypotenuse of the triangle?
-/

theorem geometry_94784
  {a b c : ℝ}
  (ha : a > 0)
  (hb : b > 0)
  (hc : c > 0)
  (h : a^2 + b^2 = c^2)
  (h1 : (1/3) * π * a^2 * b = 800 * π)
  (h2 : (1/3) * π * b^2 * a = 1920 * π)
  : c = 26
:= by
  -- Divide the two similar looking conditions for a ratio
  have : b / a = 12 / 5 := by
    calc
      b / a = ((1/3) * π * b^2 * a) / ((1/3) * π * a^2 * b) := by
        field_simp
        repeat rw [mul_assoc]
        ring
      _ = 12 / 5 := by
        rw [h1, h2]
        field_simp
        ring
  have : b = (12 / 5) * a := by
    symm at this ⊢
    simpa [← eq_div_iff (by linarith : a ≠ 0)] using this
  rw [this] at h1
  -- Substitute back to solve one fo the variables
  have h1 : a^3 = 1000 := by
    symm
    calc
      1000 = (800 * π) * (5 / (4 * π)):= by
        field_simp
        ring
      _ = 1 / 3 * π * a ^ 2 * (12 / 5 * a) * (5 / (4 * π)) := by
        rw [← h1]
      _ = a^3 := by
        field_simp
        ring
  have h1 : a = 10 := by
    rw [(by norm_num : (1000 : ℝ) = 10^3), pow_left_inj₀] at h1
    simpa
    all_goals linarith
  -- Obtain the other side by using the ratio
  have h2 : b = 24 := by
    rw [h1, (by norm_num : (12 : ℝ) / 5 * 10 = 24)] at this
    simpa
  -- Evaluate using Pythagoras'
  have h : c^2 = 676 := by
    rw [h1, h2] at h
    calc
      c^2 = 10 ^ 2 + 24 ^ 2 := by
        rw [← h]
      _ = 676 := by
        norm_num
  have h : c = 26 := by
    rw [(by norm_num : (676 : ℝ) = 26^2), pow_left_inj₀] at h
    simpa
    all_goals linarith
  simpa