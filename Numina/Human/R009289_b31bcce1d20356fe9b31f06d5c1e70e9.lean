import Mathlib
open Mathlib
/--
Kate rode her bicycle for 30 minutes at a speed of 16 mph, then walked for 90 minutes at a speed of 4 mph. What was her overall average speed in miles per hour?
-/
lemma calculus_1180 : (((30 : ℚ) / 60) * 16 + ((90 : ℚ) / 60) * 4 : ℚ) / ((30 + 90 : ℚ) / (60 : ℚ)) = 7 := by native_decide