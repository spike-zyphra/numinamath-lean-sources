import Mathlib

/-Let a,b,c denote the side lengths of BC,CA,AB. 
Find the lengths of AE,BF,CD in terms of a,b,c.-/

theorem geometry_608363 (a b c x y z : ℝ)
    (h1 : a = y + z) (h2 : b = x + z) (h3 : c = x + y) :
    x = (b + c - a) / 2 ∧ y = (a + c - b) / 2 ∧ z = (a + b - c) / 2 := by

    constructor
    .
      nlinarith
    .
      constructor
      .
        nlinarith
      .
        nlinarith