import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem algebra_145797 {f : (ℝ × ℝ) → (ℝ × ℝ)}
  (hf : ∀ x y, f (x, y) = (x + y, 2 * x + 2 * y)) :
  ∃ φ : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ), ∀ x y, f (x, y) = φ (x, y) := by 
  use { toFun := fun v => (v.1 + v.2, 2 * v.1 + 2 * v.2),
        map_add' := by 
          intro a b
          simp [Prod.ext_iff]
          all_goals 
            constructor <;> try { ring }
        , map_smul' := by 
          intro c a
          simp [Prod.ext_iff]
          all_goals 
            constructor <;> try { ring }
      }
  intro x y 
  simp [hf]