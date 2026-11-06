import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_319050 (f : ℝ → ℝ) (m : ℝ)
  (h₀ : ∀ x, f x = x^3 - 3 * x + m)
  (h₁ : ∀ a b c, a ∈ Icc 0 2 → b ∈ Icc 0 2 → c ∈ Icc 0 2 →
    ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y > z ∧ y + z > x ∧ z + x > y ∧
      x = f a ∧ y = f b ∧ z = f c) :
  m > 6 := by 
  by_contra h
  push_neg at h
  
  have h2 := h₁ 1 1 2 (by norm_num) (by norm_num) (by norm_num)
  rcases h2 with ⟨x, y, z, hx, hy, hz, hxy1, hyz1, hzx1, h2_eq, h3_eq, h4_eq⟩
  
  have eq1 : x = m - 2 := by
    rw [h2_eq]
    rw [h₀ 1]
    ring
  
  have eq2 : y = m - 2 := by
    rw [h3_eq]
    rw [h₀ 1]
    ring
  
  have eq3 : z = m + 2 := by
    rw [h4_eq]
    rw [h₀ 2]
    ring
  
  rw [eq1, eq2, eq3] at hxy1
  
  linarith