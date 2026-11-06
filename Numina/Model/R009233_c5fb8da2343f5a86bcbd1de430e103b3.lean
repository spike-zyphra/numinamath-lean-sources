import Mathlib

theorem algebra_12978 {total_dishes meatless_dishes gluten_dishes ok_dishes : ℕ}
    (h1 : total_dishes ≠ 0)
    (h2 : meatless_dishes = 4)
    (h3 : meatless_dishes * 5 = total_dishes)
    (h4 : gluten_dishes = 3)
    (h5 : ok_dishes + gluten_dishes = meatless_dishes) :
    (ok_dishes / total_dishes : ℝ) = 1 / 20 := by
  have h6 : total_dishes = 20 := by
    calc
      total_dishes = meatless_dishes * 5 := by 
        omega
      _ = 4 * 5 := by 
        rw [h2]
      _ = 20 := by 
        norm_num
  have h7 : ok_dishes = 1 := by
    -- From h5: ok_dishes + gluten_dishes = meatless_dishes
    -- From h4: gluten_dishes = 3
    -- From h2: meatless_dishes = 4
    -- Therefore: ok_dishes + 3 = 4
    -- So ok_dishes = 1
    omega
  have h8 : (ok_dishes : ℝ) / (total_dishes : ℝ) = (1 / 20 : ℝ) := by
    rw [h7, h6]
    all_goals norm_num
  exact_mod_cast h8