import Mathlib
open Real

/- As Emily is riding her bicycle on a long straight road, she spots Emerson skating
in the same direction 1/2 mile in front of her. After she passes him, she can see him
in her rear mirror until he is 1/2 mile behind her. Emily rides at a constant rate of 12
miles per hour, and Emerson skates at a constant rate of 8 miles per hour. For how
many minutes can Emily see Emerson?
(A) 6 (B) 8 (C) 12 (D) 15 (E) 16 -/
theorem algebra_97169 (emily emerson : ℚ)
(h₂ : emily = 12) (h₃ : emerson = 8) :
(1/2 + 1/2)/(emily - emerson) * 60 = 15 := by 
  -- solve by simplification
  field_simp [*];norm_num