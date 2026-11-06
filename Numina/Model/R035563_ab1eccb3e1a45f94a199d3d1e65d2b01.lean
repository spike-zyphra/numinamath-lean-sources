import Mathlib

open Real

theorem algebra_172377 :
    {(x, y, z) : ℝ × ℝ × ℝ | x = 2018 - 2019 * (if y + z > 0 then 1 else (if y + z = 0 then 0 else -1)) ∧
      y = 2018 - 2019 * (if z + x > 0 then 1 else (if z + x = 0 then 0 else -1)) ∧
      z = 2018 - 2019 * (if x + y > 0 then 1 else (if x + y = 0 then 0 else -1))}.ncard = 3 := by
  have h1 : {(x, y, z) : ℝ × ℝ × ℝ | x = 2018 - 2019 * (if y + z > 0 then 1 else (if y + z = 0 then 0 else -1)) ∧
      y = 2018 - 2019 * (if z + x > 0 then 1 else (if z + x = 0 then 0 else -1)) ∧
      z = 2018 - 2019 * (if x + y > 0 then 1 else (if x + y = 0 then 0 else -1))} = {(-1, 4037, -1), (-1, -1, 4037), (4037, -1, -1)} := by
    ext ⟨x, y, z⟩
    simp
    constructor
    · -- Assume (x, y, z) satisfies the system of equations, show it's one of the three solutions
      rintro ⟨hx, hy, hz⟩
      split_ifs at hx hy hz <;> norm_num at hx hy hz <;> 
        try { 
          norm_num [hx, hy, hz] at *
          <;> tauto
        }
    · -- Show that these three triples satisfy the system of equations
      rintro (h | h | h)
      · -- First solution
        rcases h with ⟨rfl, rfl, rfl⟩
        norm_num
      · -- Second solution
        rcases h with ⟨rfl, rfl, rfl⟩
        norm_num
      · -- Third solution
        rcases h with ⟨rfl, rfl, rfl⟩
        norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> norm_num