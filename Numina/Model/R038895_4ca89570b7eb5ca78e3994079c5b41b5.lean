import Mathlib

theorem number_theory_231638 :
    ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x^2 + y^2 + z^2 = 15129 ∧
    ∃ w x y z u v, w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ w ≠ u ∧ w ≠ v ∧
      x ≠ y ∧ x ≠ z ∧ x ≠ u ∧ x ≠ v ∧ y ≠ z ∧ y ≠ u ∧ y ≠ v ∧
      z ≠ u ∧ z ≠ v ∧ u ≠ v ∧ w^2 + x^2 + y^2 + z^2 + u^2 + v^2 = 378225 := by
  use 27
  use 72
  use 96
  constructor
  · -- Show x ≠ y
    norm_num
  constructor
  · -- Show y ≠ z
    norm_num
  constructor
  · -- Show z ≠ x
    norm_num
  constructor
  · -- Show x^2 + y^2 + z^2 = 15129
    norm_num
  use 6
  use 8
  use 66
  use 88
  use 363
  use 484
  constructor
  · -- Show w ≠ x
    norm_num
  constructor
  · -- Show w ≠ y
    norm_num
  constructor
  · -- Show w ≠ z
    norm_num
  constructor
  · -- Show w ≠ u
    norm_num
  constructor
  · -- Show w ≠ v
    norm_num
  constructor
  · -- Show x ≠ y
    norm_num
  constructor
  · -- Show x ≠ z
    norm_num
  constructor
  · -- Show x ≠ u
    norm_num
  constructor
  · -- Show x ≠ v
    norm_num
  constructor
  · -- Show y ≠ z
    norm_num
  constructor
  · -- Show y ≠ u
    norm_num
  constructor
  · -- Show y ≠ v
    norm_num
  constructor
  · -- Show z ≠ u
    norm_num
  constructor
  · -- Show z ≠ v
    norm_num
  constructor
  · -- Show u ≠ v
    norm_num
  · -- Show w^2 + x^2 + y^2 + z^2 + u^2 + v^2 = 378225
    norm_num