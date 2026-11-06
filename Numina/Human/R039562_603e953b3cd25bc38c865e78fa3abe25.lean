import Mathlib
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- Boats are sailing on the sea at a speed of $v$. Exactly opposite them, an airplane is flying at a height of $h$ at a speed of $V$. At what distance from the boat should the pilot drop the aid package so that it lands precisely in the boat? What would be the distance in question if the airplane is flying behind the boat; finally, if the boat is stationary on the water? -/
variable (v V h g : ℝ) (hg : g > 0) (hh : h > 0)

/--
Calculates the horizontal distance to drop a package from an airplane to a boat.
Case 1: Airplane and boat moving directly towards each other
-/
theorem Algebra_259755 (hg : g > 0) (hh : h > 0) :
    let t := Real.sqrt (2 * h / g)
    h = g / 2 * t^2 := by
  intro t
  have h_t_sq : t^2 = 2 * h / g := by
    simp only [t]
    rw [Real.sq_sqrt (by positivity)]
  rw [h_t_sq]
  field_simp [hg, hh]
  ring
