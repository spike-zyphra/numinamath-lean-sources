import Mathlib

theorem number_theory_248984: {n: ℤ | ∃ x y z, 0 < x ∧ x < 10 ∧ 0 < y ∧ y < 10 ∧ 0 < z ∧ z < 10 ∧
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ n = 100 * x + 10 * y + z ∧
  5 * n = (100 * x + 10 * z + y) + (100 * y + 10 * x + z) + (100 * y + 10 * z + x) +
  (100 * z + 10 * y + x) + (100 * z + 10 * x + y)} = {481, 518, 592, 629}:= by
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First direction: if n exists with that property, then n is one of 481, 518, 592, 629
    rintro ⟨x, y, z, hx0, hx1, hy0, hy1, hz0, hz1, hxy, hxz, hyz, hn, heq⟩
    have h1 : n = 100 * x + 10 * y + z := by 
      omega
    have eq3 : 7 * x = 3 * y + 4 * z := by 
      omega 
    have eq4 : x < 10 := by 
      omega 
    have eq5 : y < 10 := by 
      omega 
    have eq6 : z < 10 := by 
      omega 
    have eq7 : x > 0 := by 
      omega 
    have eq8 : y > 0 := by 
      omega 
    have eq9 : z > 0 := by 
      omega 
    interval_cases x <;> interval_cases y <;> interval_cases z 
      <;> omega 
  · -- Second direction: if n is in {481, 518, 592, 629}, then it exists 
    rintro (rfl | rfl | rfl | rfl)
    · -- n = 481
      use 4, 8, 1 
      all_goals norm_num 
    · -- n = 518 
      use 5, 1, 8 
      all_goals norm_num 
    · -- n = 592
      use 5, 9, 2 
      all_goals norm_num 
    · -- n = 629
      use 6, 2, 9 
      all_goals norm_num