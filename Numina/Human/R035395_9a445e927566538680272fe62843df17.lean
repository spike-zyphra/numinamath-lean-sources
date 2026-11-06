import Mathlib

open Real Set
open scoped BigOperators

/-The value range of the function $f(x) = \tan x$, where $x \in \left[0, \frac{\pi}{4}\right]$, is __________.-/
theorem algebra_9277 (f : ℝ → ℝ) (hf : f = tan) (x : ℝ) (hx : x ∈ Icc 0 (π/4)) :
  f x ∈ Icc 0 1 := by
    -- The function $f(x) = \tan x$ is a monotonically increasing function on the
    -- interval $x \in \left[0, \frac{\pi}{4}\right]$
    have h1 : StrictMonoOn f (Icc 0 (π/4)) := by
      have := Real.strictMonoOn_tan
      exact StrictMonoOn.mono (hf ▸ Real.strictMonoOn_tan)
        (Icc_subset_Ioo (by simp [Real.pi_pos]) ((div_lt_div_iff (by simp) (by simp)).2
          ((mul_lt_mul_left (Real.pi_pos)).mpr (by norm_cast))))
    -- we have $\tan 0 \leq \tan x \leq \tan \frac{\pi}{4}$,
    -- which means $0 \leq \tan x \leq 1$, Therefore, the value range of the function $f(x)$ on $\left[0, \frac{\pi}{4}\right]$ is $[0, 1]$.
    -- Hence, the answer is: $\boxed{[0, 1]}$.
    have := MonotoneOn.mapsTo_Icc (StrictMonoOn.monotoneOn h1)
    specialize this hx
    convert this <;> simp [hf]
