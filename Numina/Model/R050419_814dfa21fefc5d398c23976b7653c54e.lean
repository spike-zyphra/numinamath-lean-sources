import Mathlib

open Polynomial

/- If ${{a}^{2}}-3a+1=0$, then the value of $\frac{{{a}^{3}}}{{{a}^{6}}+1}$ is ___          ___. -/
theorem algebra_1612 {a : ℝ} (p : ℝ[X]) (hp : p = X^2 + C (-3) * X + C 1) (ha : p.eval a = 0) : a^3 / (a^6 + 1) = 1 / 18 := by
  have h1 : a^2 = 3 * a - 1 := by
    simp [hp] at ha
    linarith

  have h2 : a^3 = 8 * a - 3 := by
    calc
      a^3 = a * a^2 := by ring
      _ = a * (3 * a - 1) := by rw [h1]
      _ = 3 * a^2 - a := by ring
      _ = 3 * (3 * a - 1) - a := by rw [h1]
      _ = 9 * a - 3 - a := by ring
      _ = 8 * a - 3 := by ring

  have h3 : a^6 = 144 * a - 55 := by
    calc
      a^6 = a^2 * a^4 := by ring
      _ = a^2 * (a * a^3) := by ring
      _ = a^2 * (a * (8 * a - 3)) := by rw [h2]
      _ = a^2 * (8 * a^2 - 3 * a) := by ring
      _ = a^2 * (8 * (3 * a - 1) - 3 * a) := by rw [h1]
      _ = a^2 * (24 * a - 8 - 3 * a) := by ring
      _ = a^2 * (21 * a - 8) := by ring
      _ = (3 * a - 1) * (21 * a - 8) := by rw [h1]
      _ = 3 * a * (21 * a - 8) - 1 * (21 * a - 8) := by ring
      _ = (63 * a^2 - 24 * a) - (21 * a - 8) := by ring
      _ = (63 * (3 * a - 1) - 24 * a) - (21 * a - 8) := by rw [h1]
      _ = (189 * a - 63 - 24 * a) - (21 * a - 8) := by ring
      _ = (165 * a - 63) - (21 * a - 8) := by ring
      _ = 144 * a - 55 := by ring

  have h5 : a^6 + 1 = 18 * (8 * a - 3) := by
    calc
      a^6 + 1 = (144 * a - 55) + 1 := by rw [h3]
      _ = 144 * a - 54 := by ring
      _ = 18 * (8 * a - 3) := by ring

  have h6 : 8 * a - 3 ≠ 0 := by
    by_contra h
    have h7 : a = 3 / 8 := by linarith
    rw [h7] at ha
    simp [hp] at ha
    norm_num at ha

  rw [h5, h2]
  field_simp [h6]
  <;> nlinarith [sq_nonneg (a - 3 * a / 2), sq_nonneg (a - 3 / (2 : ℝ))]