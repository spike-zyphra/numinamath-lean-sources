import Mathlib

theorem algebra_605055 :
  {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a * b + c + d = 3 ∧ b * c + d + a = 5 ∧ c * d + a + b = 2 ∧ d * a + b + c = 6} =
    {(2, 0, 0, 3)} := by
  ext ⟨a, b, c, d⟩
  simp
  constructor
  · -- First, we prove that if $(a, b, c, d)$ satisfies all four equations, then $(a, b, c, d) = (2, 0, 0, 3)$.
    rintro ⟨h1, h2, h3, h4⟩
    have h5 : (a - 1) * (d - b) = 3 := by
      nlinarith
    have h6 : (b - d) * (c - 1) = 3 := by
      nlinarith
    have h7 : (d - b) * (a + c - 2) = 0 := by
      nlinarith [h5, h6]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case where $d - b = 0$
      have h10 : d - b = 0 := by linarith
      have h11 : (a - 1) * (d - b) = 0 := by
        rw [h10]
        ring
      linarith
    · -- Case where $a + c - 2 = 0$
      have h12 : a + c - 2 = 0 := by linarith
      have h13 : c = 2 - a := by linarith
      have h14 : d = a - a * b + 1 := by
        rw [h13] at h1
        nlinarith
      have ha : a = 2 := by
        nlinarith [h1, h2, h3, h4, h14, h13]
      have hb : b = 0 := by
        rw [ha] at h1
        nlinarith [h1, h2, h3, h4]
      have hc : c = 0 := by
        rw [ha, hb] at h2
        nlinarith [h1, h2, h3, h4]
      have hd : d = 3 := by
        rw [ha, hb, hc] at h1
        nlinarith [h1, h2, h3, h4]
      exact ⟨ha, hb, hc, hd⟩
  · -- Now we prove that $(2, 0, 0, 3)$ indeed satisfies all four equations.
    rintro ⟨rfl, rfl, rfl, rfl⟩
    norm_num