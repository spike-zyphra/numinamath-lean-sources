import Mathlib

theorem algebra_164530 (total_potatoes : ℝ) (h : total_potatoes = 15000)
    (students : ℝ) (farmers_with_combine : ℝ) (other_farmers : ℝ)
    (h1 : students = total_potatoes * (1 / 5)) (h2 : farmers_with_combine = total_potatoes * (1 / 3))
    (h3 : other_farmers = total_potatoes - students - farmers_with_combine) :
    students = 3000 ∧ farmers_with_combine = 5000 ∧ other_farmers = 7000 := by
  constructor
  · -- Prove students = 3000
    rw [h1]
    rw [h]
    norm_num
  constructor
  · -- Prove farmers_with_combine = 5000
    rw [h2]
    rw [h]
    norm_num
  · -- Prove other_farmers = 7000
    rw [h3]
    have h3a : students = 3000 := by
      rw [h1]
      rw [h]
      norm_num
    have h3b : farmers_with_combine = 5000 := by
      rw [h2]
      rw [h]
      norm_num
    rw [h, h3a, h3b]
    norm_num