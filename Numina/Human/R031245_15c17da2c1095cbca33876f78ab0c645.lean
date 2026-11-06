import Mathlib

open Real intervalIntegral

/- 665. A rectangular reservoir with a horizontal cross-sectional area of $S=6 \mathrm{~m}^{2}$ is filled with water to a height of $H=5$ m. Determine the time it takes for all the water to flow out of the reservoir through a small hole in its bottom with an area of $s=0.01 \mu^{2}$, assuming that the velocity of the water flow is $0.6 \sqrt{2 \text { g } h}$, where $h$ is the height of the water level above the hole, and $g$ is the acceleration due to gravity. -/
theorem algebra_185569 (g s H S : NNReal) :
    S / (0.6 * s * sqrt (2 * g)) * ∫ x : ℝ in (0)..H, (H - x)^(-1/2 : ℝ) = 2 * S / (0.6 * s) * sqrt (H / (2 * g)) := by
    -- Swap the bounds of the integral and compute it
    rw [integral_comp_sub_left fun x => x^(-1/2 : ℝ), integral_rpow (by left; linarith)]
    -- Clean up the result
    norm_num
    rw [←sqrt_eq_rpow]
    ring