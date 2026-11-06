import Mathlib

/-
Some students are taking a math contest, in which each student takes one of four tests. One third of the students take one test, one fourth take another test, one fifth take the next test, and 26 students take the last test. How many students are taking the contest in total?
-/
theorem algebra_610875 {n : ℝ} (h1 : n / 3 + n / 4 + n / 5 + 26 = n) : n = 120 := by
  -- This is a module question, thus the answer of this is really simple in mathematics, the hard thing is how to formulate the natural language question into mathematics language.
  ring_nf at h1
  have _1 : n = 120 := by linarith
  exact _1
