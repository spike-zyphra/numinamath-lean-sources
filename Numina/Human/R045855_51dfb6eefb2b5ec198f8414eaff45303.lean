import Mathlib

open Real Set
open scoped BigOperators

/- 8. $[a]$ represents the greatest integer not exceeding $a$, the maximum value of the function $f(x)=\left|\frac{1}{x}-\left[\frac{1}{x}+\frac{1}{2}\right]\right|$ is . $\qquad$ -/
theorem algebra_198282 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = abs (1 / x - ⌊1 / x + 1 / 2⌋)) :
  IsGreatest (range f) (1 / 2) := by
  constructor
    -- 1/2 is in range by pluggin in 3/2
  . use (2/3:ℝ)
    rw [h₀]
    norm_num
    -- to prove 1/2 is a lower bound, we'll prove -1/2 ≤ 1/x - ⌊1/x + 1/2⌋ ≤ 1/2
  . rintro h ⟨x, hx⟩
    rw [← hx, h₀]
    apply abs_le.mpr
    -- left inequality proved by the fact that ⌊y⌋ ≤ y
    -- right inequality proved by the fact that y < ⌊y⌋ + 1
    and_intros
    . linarith only [Int.floor_le (1/x + 1/2)]
    . linarith only [Int.lt_floor_add_one (1/x + 1/2)]