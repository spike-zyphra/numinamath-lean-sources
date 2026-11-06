import Mathlib

theorem algebra_309722 (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : x = a / (2 * b + 3 * c)) (h' : y = 2 * b / (3 * c + a)) (h'' : z = 3 * c / (a + 2 * b)) :
    x / (1 + x) + y / (1 + y) + z / (1 + z) = 1 := by 
  have hx1 : 1 + x = (a + 2 * b + 3 * c) / (2 * b + 3 * c) := by
    rw [h]
    field_simp
    <;> ring

  have h1 : x / (1 + x) = a / (a + 2 * b + 3 * c) := by
    rw [hx1, h]
    field_simp
    <;> ring
  
  have hy1 : 1 + y = (a + 2 * b + 3 * c) / (3 * c + a) := by
    rw [h']
    field_simp
    <;> ring

  have h2 : y / (1 + y) = 2 * b / (a + 2 * b + 3 * c) := by
    rw [hy1, h']
    field_simp
    <;> ring

  have hz1 : 1 + z = (a + 2 * b + 3 * c) / (a + 2 * b) := by
    rw [h'']
    field_simp
    <;> ring

  have h3 : z / (1 + z) = 3 * c / (a + 2 * b + 3 * c) := by
    rw [hz1, h'']
    field_simp
    <;> ring
  
  rw [h1, h2, h3]
  have h4 : a / (a + 2 * b + 3 * c) + 2 * b / (a + 2 * b + 3 * c) + 3 * c / (a + 2 * b + 3 * c) = 1 := by
    have h5 : a + 2 * b + 3 * c ≠ 0 := by positivity
    field_simp [h5]
    <;> ring
  
  exact h4