import Mathlib

-- Define the inequality function
def linearInequality (x : ℝ) : Prop := 2 * x - 6 < 0

-- Define the solution set
def solutionSet : Set ℝ := {x | x < 3}

/-Express the solution set of the inequality $2x-6<0$ using the descriptive method.-/
theorem algebra_9220 :
  {x : ℝ | linearInequality x} = solutionSet := by
  -- The inequality 2x-6 < 0 is equivalent to x < 3
  have inequality_equivalence (x : ℝ) :
  linearInequality x ↔ x < 3 := by
    unfold linearInequality
    constructor
    · intro h
      -- From 2x - 6 < 0 to x < 3
      have h1 : 2 * x < 6 := by linarith
      have h2 : x < 3 := by
        have :2 * x - 6 =2 * x -2*3:=by norm_num
        rw [this] at h
        apply lt_of_sub_neg at h
        simp at h
        exact h
      exact h2
    · intro h
      -- From x < 3 to 2x - 6 < 0
      have h1 : 2 * x < 2 * 3 := by
        simp only [Nat.ofNat_pos, mul_lt_mul_left]
        exact h
      have h2 :(2 : ℝ)* 3 = 6 := by ring
      have h3 : 2 * x < 6 := by
        apply lt_of_lt_of_eq h1 h2
      linarith
  ext x
  exact inequality_equivalence x
