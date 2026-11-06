import Mathlib

open Finset

theorem other_6946 {a b : ℕ} (ha : a = 0b11101) (hb : b = 0b1011) : a - b = 0b10010 := by
  subst ha
  subst hb
  all_goals omega