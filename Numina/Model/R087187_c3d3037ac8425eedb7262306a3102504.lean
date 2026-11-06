import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem algebra_1151 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] [FiniteDimensional F V] {L : V →ₗ[F] V} :
  Function.Injective L ↔ Function.Surjective L := by
  apply LinearMap.injective_iff_surjective