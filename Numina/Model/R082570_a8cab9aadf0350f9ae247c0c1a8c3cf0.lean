import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_140238
  (a b : ℝ × ℝ × ℝ)
  (ha : a = (2, 5, -1))
  (hb : b = (1, -1, -3)) :
  let a_length := Real.sqrt (2^2 + 5^2 + (-1)^2)
  let b_length := Real.sqrt (1^2 + (-1)^2 + (-3)^2)
  let a_b_product := (2 * 1 + 5 * (-1) + (-1) * (-3))
  a_length = Real.sqrt 30 ∧ b_length = Real.sqrt 11 ∧ a_b_product = 0 := by
  constructor
  · -- Show that a_length = Real.sqrt 30
    norm_num
  constructor
  · -- Show that b_length = Real.sqrt 11
    norm_num
  · -- Show that a_b_product = 0
    norm_num