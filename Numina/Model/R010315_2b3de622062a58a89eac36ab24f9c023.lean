import Mathlib

-- Define the inequality function
def linearInequality (x : ℝ) : Prop := 2 * x - 6 < 0

-- Define the solution set
def solutionSet : Set ℝ := {x | x < 3}

theorem algebra_9220 :
  {x : ℝ | linearInequality x} = solutionSet := by
  ext x
  simp [linearInequality, solutionSet]
  constructor
  . -- Forward: if $2x - 6 < 0$ then $x < 3$.
    intro h
    linarith
  . -- Backward: if $x < 3$ then $2x - 6 < 0$.
    intro h
    linarith