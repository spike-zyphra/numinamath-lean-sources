import Mathlib

/-Lincoln Elementary School has 120 students. Of these 120 students, $\frac{2}{5}$ ride the bus to school and $\frac{5}{12}$ have a parent drive them to school. If the rest of the students walk to school, what fraction of students walk to school?-/
theorem algebra_21632 (total_students : ℕ) (h : total_students = 120)
    (bus_riders : ℚ) (h_bus_riders : bus_riders = 2 / 5) (parent_drivers : ℚ)
    (h_parent_drivers : parent_drivers = 5 / 12) :
    (total_students - (bus_riders * total_students) - (parent_drivers * total_students)) / total_students =
    11 / 60 := by
  rw [h, h_parent_drivers, h_bus_riders]
  norm_num
