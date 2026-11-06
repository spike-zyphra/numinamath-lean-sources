import Mathlib

/- My date tonight made reservations for us at his favorite Italian restaurant.  He didn't know that I am a vegetarian with a gluten allergy.  There are four dishes here without meat in them.  That's just one fifth of the menu.  And three of those meatless dishes are made with pasta, which contains gluten.  What fraction of the items on the menu at this restaurant can I eat? -/
theorem algebra_12978 {total_dishes meatless_dishes gluten_dishes ok_dishes : ℕ}
    (h1 : total_dishes ≠ 0)
    (h2 : meatless_dishes = 4)
    (h3 : meatless_dishes * 5 = total_dishes)
    (h4 : gluten_dishes = 3)
    (h5 : ok_dishes + gluten_dishes = meatless_dishes) :
    (ok_dishes / total_dishes : ℝ) = 1 / 20 := by
  simp_all
  norm_cast
  simp_all