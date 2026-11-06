import Mathlib

open Real Set
open scoped Real

theorem algebra_9026 : IsLeast {x | ∃ t, x = sin t * cos t} (-1/2) := by
constructor
-- first prove x=pi/4 is ok
use -(Real.pi/4)
simp
field_simp
-- prove it is lower bounds
rw [mem_lowerBounds]
intro x hx
-- prove sint cost>-1/2
simp at hx
rcases hx with ⟨t,ht⟩
rw [ht]
-- simp sint cost
have ht2:= Real.sin_two_mul t
have ht3:= Real.neg_one_le_sin (2 * t)
linarith