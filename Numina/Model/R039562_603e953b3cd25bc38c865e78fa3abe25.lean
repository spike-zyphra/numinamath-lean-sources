import Mathlib
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/- Boats are sailing on the sea at a speed of $v$. Exactly opposite them, an airplane is flying at a height of $h$ at a speed of $V$. At what distance from the boat should the pilot drop the aid package so that it lands precisely in the boat? What would be the distance in question if the airplane is flying behind the boat; finally, if the boat is stationary on the water? -/
variable (v V h g : ℝ) (hg : g > 0) (hh : h > 0)

theorem Algebra_259755 (hg : g > 0) (hh : h > 0) :
    let t := Real.sqrt (2 * h / g)
    h = g / 2 * t^2 := by
  intro t 
  have ht2 : t ^ 2 = 2 * h / g := by 
    rw [Real.sq_sqrt]
    have h1 : (2 * h / g) ≥ 0 := by 
      apply div_nonneg
      linarith
      linarith
    linarith 
  -- Now we need to prove h = g / 2 * t^2 
  have eq1 : h = g / 2 * t^2 := by 
    -- From ht2, we have t ^ 2 = 2 * h / g 
    -- Multiply both sides by g / 2 
    -- So h = (g / 2) * t ^ 2 
    have eq2 : t ^ 2 = 2 * h / g := ht2 
    field_simp at eq2 ⊢ 
    nlinarith [eq2] 
  linarith [eq1]