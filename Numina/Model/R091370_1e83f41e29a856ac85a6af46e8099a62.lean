import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem algebra_138268 {G H I : Type*} [Group G] [Group H] [Group I]
  (φ : G →* H) (ψ : H →* I) :
  ∃ φ' : G →* I, ∀ g : G, φ' g = ψ (φ g) := by
  use ψ.comp φ
  intro g
  simp