import Mathlib
open Mathlib
lemma algebra_1173 (cougars panthers : ℕ) (h1 : cougars + panthers = 34) (h2 : cougars = panthers + 14) : panthers = 10 := by
  rw [h2] at h1
  omega