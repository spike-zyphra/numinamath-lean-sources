import Mathlib

/-For a designer suit, Daniel must specify his waist size in centimeters. If there are $12$ inches in a foot and $30.5$ centimeters in a foot, then what size should Daniel specify, in centimeters, if his waist size in inches is $34$ inches?  (You may use a calculator on this problem; answer to the nearest tenth.)-/
theorem algebra_14085 (h1: ft_to_inches = (12:ℚ)) (h2: ft_to_cm = 30.5)
(h3: inches_to_cm = ft_to_cm / ft_to_inches)(h4: waist_in_inches = (34:ℚ))
(h5: (rounded_waist_in_cm : ℚ) = (round (inches_to_cm * waist_in_inches * 10)) / 10) :
rounded_waist_in_cm = 86.4 := 
-- This is a straightforward computation by applying round_eq
by rw [h5, h4, h3, h2, h1, round_eq]; norm_num