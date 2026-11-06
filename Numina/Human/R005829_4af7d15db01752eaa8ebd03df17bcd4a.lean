import Mathlib


/-
For breakfast, Mihir always eats a bowl of Lucky Charms cereal, which consists of oat pieces and marshmallow pieces. He defines the luckiness of a bowl of cereal to be the ratio of the number of marshmallow pieces to the total number of pieces. One day, Mihir notices that his breakfast cereal has exactly 90 oat pieces and 9 marshmallow pieces, and exclaims, "This is such an unlucky bowl!" How many marshmallow pieces does Mihir need to add to his bowl to double its luckiness?
-/
def lucky_charms (o m : ℕ) := (m : ℚ) / (o + m)

theorem algebra_610103 (x : ℕ) (hoat: oat = 90) (hmarshmallow: marshmallow = 9) (h2times : (lucky_charms marshmallow oat) * (2:ℚ) =  lucky_charms (x + marshmallow) oat) : x = 11  := by
  
  -- Substituting the given values for the variables.
  rw [hoat, hmarshmallow] at h2times

  -- Unfold definitions in `lucky_charms`.
  unfold lucky_charms at h2times

  -- Simplify the rational equation from `h2times` using field simplification
  field_simp at h2times
  ring_nf at h2times

  -- Calcuating final expression and solving for x
  linarith

