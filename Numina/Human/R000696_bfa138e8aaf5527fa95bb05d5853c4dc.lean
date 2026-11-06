import Mathlib

/- The average of 10 numbers is 85. If the numbers 70 and 76 are removed from the set of numbers, what is the average of the remaining numbers? -/
theorem algebra_6559 (S : Multiset ℝ) (cardS : Multiset.card S = 10) (sumS : Multiset.sum S / Multiset.card S = 85) (hS : {70, 76} ≤ S) :
    Multiset.sum (S - ({70, 76} : Multiset ℝ)) / Multiset.card (S - ({70, 76} : Multiset ℝ)) = 88 := by
  -- Set T to be the set S after removing 70 and 76
  let T := S - ({70, 76} : Multiset ℝ)
  -- Show that the card of T is 8
  have cardT : Multiset.card T = 8 := by
    -- Use the fact that S has 10 elements and 70 and 76 are in S
    rw [Multiset.card_sub hS, cardS]
    simp

  -- Show that the sum of S is 850
  replace sumS : Multiset.sum S = 850 := by
    -- S.sum / S.card = S.sum / 10 = 85
    rw [cardS] at sumS
    field_simp at sumS
    norm_num at sumS
    exact sumS

  -- Show that the sum of T is 704
  have sumT : Multiset.sum T = 704 := by
    -- T + {70, 76} = S
    have h : T + ({70, 76} : Multiset ℝ) = S := tsub_add_cancel_of_le hS
    -- Apply the sum function to both sides
    apply_fun Multiset.sum at h
    -- Use the fact that the sum of S is 850
    rw [Multiset.sum_add] at h
    -- Simplify the equation
    simp [sumS] at h
    linarith only [h]

  -- Put the pieces together
  rw [cardT, sumT]
  norm_num
