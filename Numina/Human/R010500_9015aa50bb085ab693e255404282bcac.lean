import Mathlib
/-Given the power function $f(x)=(m-2)x^{m^2-2m}$, find $m$.-/
theorem algebra_9062 (m:ℝ)(hf:∃ (a:ℝ),∀ (x:ℝ), (x^a) =  (m - 2) * x^(m^2 - 2 * m)) :m = 3 := by 
    rcases hf with ⟨a,ha⟩
    -- intro condition
    have ha1:= ha 1
    -- use x=1
    simp at ha1
    -- solve ha1
    linarith

