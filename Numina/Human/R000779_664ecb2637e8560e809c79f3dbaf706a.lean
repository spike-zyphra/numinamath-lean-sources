import Mathlib

/- Out of 1200 people polled, $30\%$ do not like radio, and $10\%$ of the people who do not like radio also do not like music.  How many people polled do not like both radio and music? -/
theorem algebra_15187 {total radio music : Finset ℕ}
    (h0 : radio ⊆ total ∧ music ⊆ total)
    (h1 : total.card = 1200)
    (h2 : (total \ radio).card = (30 / 100 : ℚ) * total.card)
    (h3 : ((total \ radio) \ music).card = (10 / 100 : ℚ) * (total \ radio).card) :
    ((total \ radio) \ music).card = 36 := by
  simp_all
  norm_num at h3
  norm_cast at h3