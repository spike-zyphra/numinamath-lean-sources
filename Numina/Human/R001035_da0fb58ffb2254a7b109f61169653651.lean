import Mathlib

/-John divided his souvenir hat pins into two piles. The two piles had an equal number of pins. He gave his brother one-half of one-third of one pile. John had 66 pins left. How many pins did John originally have?-/
theorem algebra_20028 {pile : ℕ} (hx : pile ≠ 0) (h : 2 * pile - ((1 : ℝ) / 2) * (1 / 3) * pile  = 66) :
    2 * pile = 72 := by
      -- Initially, John has $2a$ pins, where $a$ is the number of pins in each pile. He gives away $\frac{a}{6}$ pins, so $2a-\frac{a}{6} = \frac{11a}{6} = 66$ is the number of pins he has left. We get $a=36$, so he originally had $2a = \boxed{72}$ pins.
      field_simp at h
      have : 2 * (pile : ℝ ) = 72 := by
        norm_num at h
        linarith
      norm_cast at this