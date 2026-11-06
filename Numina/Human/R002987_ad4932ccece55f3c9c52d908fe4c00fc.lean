import Mathlib

open Real

/- ## Task Condition

Find the derivative.

$y=(\cos 2 x)^{\ln (\cos 2 x) / 4}$ -/
theorem calculus_139752 {x : ℝ} {f : ℝ → ℝ} (hx : 0 < cos (2 * x))
    (hf : f = λ x => (cos (2 * x)) ^ (log (cos (2 * x)) / 4)) :
    HasDerivAt f (-(cos (2 * x)) ^ (log (cos (2 * x)) / 4) * tan (2 * x) * log (cos (2 * x))) x := by
  -- Define h(x) = cos(2 * x).
  set h : ℝ → ℝ := fun x => cos (2 * x)
  -- Define g(x) = log(h(x)) / 4.
  set g : ℝ → ℝ := fun x => log (h x) / 4
  -- Define h'(x) = (-sin(2 * x) * 2.
  set h' : ℝ → ℝ := fun x => (-sin (2 * x)) * 2
  -- Define g'(x) = (h'(x) / h(x)) / 4.
  set g' : ℝ → ℝ := fun x => (h' x / h x) / 4
  -- We have f(x) = h(x) ^ g(x).
  have hf_eq : f = (fun x => h x ^ g x) := by ext x; simp [hf, h, g]
  -- Show that -(cos (2 * x)) ^ (log (cos (2 * x)) / 4) * tan (2 * x) * log (cos (2 * x))
  --    = h' x * g x * h x ^ (g x - 1) + g' x * h x ^ g x * log (h x).
  have eq : -(cos (2 * x)) ^ (log (cos (2 * x)) / 4) * tan (2 * x) * log (cos (2 * x))
              = h' x * g x * h x ^ (g x - 1) + g' x * h x ^ g x * log (h x) := by
    rw [show cos (2 * x) = h x by rfl, show log (h x) / 4 = g x by rfl]
    have eq : tan (2 * x) = (-1 / 2) * h' x / h x  := by
      simp_rw [tan_eq_sin_div_cos, h', h]
      ring
    rw [eq]
    simp_rw [show log (h x) = 4 * g x by ring, g']
    rw [rpow_sub hx, rpow_one, show cos (2 * x) = h x by rfl]
    ring
  -- The derivative of h is h'.
  have dh : HasDerivAt h (h' x) x := by
    apply HasDerivAt.cos
    nth_rw 2 [show (2 : ℝ) = 2 * 1 by norm_num]
    apply HasDerivAt.const_mul
    exact hasDerivAt_id' x
  rw [hf_eq, eq]
  -- The derivative of f(x) = h(x)^g(x) is h'(x) * g(x) * h(x)^(g(x) - 1) + g'(x) * h(x)^g(x) * log(h(x))
  -- when the derivative of g is g'.
  apply HasDerivAt.rpow dh _ hx
  -- Show that the derivative of g is g'.
  apply HasDerivAt.div_const
  exact HasDerivAt.log dh (by linarith)