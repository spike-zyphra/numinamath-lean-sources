import Mathlib

theorem algebra_269242 (total_students : ℕ) (h : total_students = 400 + 600)
    (boys_in_cayley : ℕ) (girls_in_cayley : ℕ)
    (boys_in_fermat : ℕ) (girls_in_fermat : ℕ)
    (h1 : boys_in_cayley = 400 * 3 / 5) (h2 : girls_in_cayley = 400 * 2 / 5)
    (h3 : boys_in_fermat = 600 * 2 / 5) (h4 : girls_in_fermat = 600 * 3 / 5) :
    (boys_in_cayley + boys_in_fermat) * 13 = (girls_in_cayley + girls_in_fermat) * 12 := by
  have hb1 : boys_in_cayley = 240 := by
    simp [h1]
    <;> norm_num
  have hg1 : girls_in_cayley = 160 := by
    simp [h2]
    <;> norm_num
  have hb2 : boys_in_fermat = 240 := by
    simp [h3]
    <;> norm_num
  have hg2 : girls_in_fermat = 360 := by
    simp [h4]
    <;> norm_num
  calc
    (boys_in_cayley + boys_in_fermat) * 13 = (240 + 240) * 13 := by
      rw [hb1, hb2]
    _ = 480 * 13 := by norm_num
    _ = 6240 := by norm_num
    _ = 520 * 12 := by norm_num
    _ = (160 + 360) * 12 := by norm_num
    _ = (girls_in_cayley + girls_in_fermat) * 12 := by
      rw [hg1, hg2]