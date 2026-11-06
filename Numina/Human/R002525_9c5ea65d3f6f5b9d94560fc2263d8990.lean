import Mathlib

/- 
Last summer 30% of the birds living on Town Lake were geese, 25% were swans,
10% were herons, and 35% were ducks. What percent of the birds that were not
swans were geese?

(A) 20  (B) 30  (C) 40  (D) 50  (E) 60
-/ 

theorem other_94695 (total_birds : ℝ) (h : total_birds = 100)
    (geese_percentage swans_percentage herons_percentage ducks_percentage : ℝ)
    (h1 : geese_percentage = 30 / 100) (h2 : swans_percentage = 25 / 100)
    (h3 : herons_percentage = 10 / 100) (h4 : ducks_percentage = 35 / 100) :
    (geese_percentage * total_birds)
      / (total_birds - swans_percentage * total_birds)
    = 40 / 100 := by
    -- First, we substitute total_birds with 100
  rw [h]
    -- Then, we compute the percent of the birds that were not swans were geese as (geese_percentage * 100)/ (100 - swans_percentage * 100)
  calc
    (geese_percentage * 100)
      / (100 - swans_percentage * 100)
    = ((30 / 100 : ℝ) * 100)
      / (100 - (25 / 100 : ℝ) * 100) := by rw [h1, h2]
    -- Since 30/100 * 100 = 30 and 25/100 * 100 = 25, then we get
    _ = 30 / (100 - 25) := by norm_num
    -- Because 100 - 25 = 75, then
    _ = 30 / 75 := by ring
    -- Reducing, we get 30 / 75 = 0.4
    _ = 0.4 := by norm_num
    -- which is equivalent to 40/100
    _ = 40 / 100 := by norm_num