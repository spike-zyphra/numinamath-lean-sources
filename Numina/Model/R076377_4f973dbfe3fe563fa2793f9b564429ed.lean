import Mathlib

theorem algebra_11086 {total_students : ℕ} (h : total_students = 200)
    (band_students : ℕ) (h1 : band_students = 70) (chorus_students : ℕ)
    (h2 : chorus_students = 95) (band_or_chorus_students : ℕ)
    (h3 : band_or_chorus_students = 150) :
    band_students + chorus_students - band_or_chorus_students = 15 := by
  calc
    band_students + chorus_students - band_or_chorus_students
        = 70 + 95 - 150 := by rw [h1, h2, h3]
    _ = 165 - 150 := by norm_num
    _ = 15 := by norm_num