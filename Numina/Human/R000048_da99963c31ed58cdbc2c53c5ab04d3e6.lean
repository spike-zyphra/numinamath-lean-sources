import Mathlib
/-- The initial number of pencils -/
def initial_pencils : Nat := 2015

/-- The number of pencils lost -/
def lost_pencils : Nat := 5

/-- The number of pencils gained -/
def gained_pencils : Nat := 50

/-- Calculate the final number of pencils -/
def final_pencils : Nat :=
  initial_pencils - lost_pencils + gained_pencils

/-- Theorem: The final number of pencils is 2060 -/
theorem final_pencils_is_2060 : final_pencils = 2060 := by
  -- Unfold the definition of final_pencils
  unfold final_pencils
  -- Simplify the arithmetic expression
  simp [initial_pencils, lost_pencils, gained_pencils]
  -- The goal is now solved

#eval final_pencils  -- This will print 2060
