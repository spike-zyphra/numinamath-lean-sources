import Mathlib

theorem algebra_234897 {x y z n m w : ℕ}
    (h₁ : (x / y : ℝ) = 3 / 4 ∧ (y / z : ℝ) = 4 / 6)
    (h₂ : (n / m : ℝ) = 2 / 5 ∧ (m / w : ℝ) = 5 / 8)
    (h₃ : x - n ≤ 10) (h₄ : (w / z : ℝ) = 1.8) :
    x + y + z = 260 := by
  have hx : x ≠ 0 := by
    intro h
    rw [h] at h₁
    simp at h₁
    linarith
  have hy : y ≠ 0 := by
    intro h
    rw [h] at h₁
    simp at h₁
    linarith
  have hz : z ≠ 0 := by
    intro h
    rw [h] at h₁
    simp at h₁
    linarith
  have hn : n ≠ 0 := by
    intro h
    rw [h] at h₂
    simp at h₂
    linarith
  have hm : m ≠ 0 := by
    intro h
    rw [h] at h₂
    simp at h₂
    linarith
  have hw : w ≠ 0 := by
    intro h
    rw [h] at h₂
    simp at h₂
    linarith
  field_simp at *
  rw [←mul_right_inj' (show (5 : ℝ) ≠ 0 by simp), ←mul_assoc] at h₄
  norm_num at h₄
  norm_cast at *
  omega
