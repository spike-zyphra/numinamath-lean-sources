import Mathlib

theorem algebra_289024 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
  {x : ℝ | 12 * a * b * x^2 - (16 * a^2 - 9 * b^2) * x - 12 * a * b = 0} = 
  {(4*a)/(3*b), -3*b/(4*a)} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward: if 12abx² - (16a² - 9b²)x - 12ab = 0, then x = 4a/(3b) or x = -3b/(4a)
    intro h
    have h1 : 12 * a * b * x^2 - (16 * a^2 - 9 * b^2) * x - 12 * a * b = 0 := h
    have h2 : (4 * a * x + 3 * b) * (3 * b * x - 4 * a) = 0 := by
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case where 4 * a * x + 3 * b = 0
      have hx2 : x = -3 * b / (4 * a) := by
        field_simp [ha]
        linarith
      right 
      simp [hx2]
    · -- Case where 3 * b * x - 4 * a = 0
      have hx2 : x = (4 * a) / (3 * b) := by
        field_simp [hb]
        linarith
      left 
      simp [hx2]
  · -- Backward: if x = 4a/(3b) or x = -3b/(4a), then 12abx² - (16a² - 9b²)x - 12ab = 0
    rintro (hx | hx)
    · -- x = 4a/(3b)
      rw [hx]
      field_simp [hb, ha]
      <;> ring_nf 
    · -- x = -3b/(4a)
      rw [hx]
      field_simp [ha, hb]
      <;> ring_nf