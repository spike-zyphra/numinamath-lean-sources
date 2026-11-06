import Mathlib

theorem algebra_96769 {U V W X Y Z : ℤ}
(hU : U = 2 * 2004 ^ 2005) (hV : V = 2004 ^ 2005) (hW : W = 2003 * 2004 ^ 2004)
(hX : X = 2 * 2004 ^ 2004) (hY : Y = 2004 ^ 2004) (hZ : Z = 2004 ^ 2003) :
U - V > V - W ∧ U - V > W - X ∧ U - V > X - Y ∧ U - V > Y - Z := by
  -- Simplify all difference terms by norm_num
  have huv : U - V = 2004 ^ 2005 := by
    rw [hU, hV]
    norm_num
  have hvw : V - W = 2004 ^ 2004 := by
    rw [hV, hW]
    norm_num
  have hwx : W - X = 2001 * 2004 ^ 2004 := by
    rw [hW, hX]
    norm_num
  have hxy : X - Y = 2004 ^ 2004 := by
    rw [hX, hY]
    norm_num
  have hyz : Y - Z = 2003 * 2004 ^ 2003 := by
    rw [hY, hZ]
    norm_num

  -- Split the goal into components of `and`
  -- and use norm_num to prove each from the above.
  apply And.intro
  · rw [huv, hvw]
    norm_num
  · apply And.intro
    · rw [huv, hwx]
      norm_num
    · apply And.intro
      · rw [huv, hxy]
        norm_num
      · rw [huv, hyz]
        norm_num