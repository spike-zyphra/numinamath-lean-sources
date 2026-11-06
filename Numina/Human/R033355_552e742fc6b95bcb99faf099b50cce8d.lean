import Mathlib

/- The sum of the first 2011 terms of a geometric sequence is 200. The sum of
the first 4022 terms is 380. Find the sum of the first 6033 terms. -/
theorem algebra_95005 {a r : ℚ} (hr : r ≠ 0) (h1 : a * (1 - r ^ 2011) / (1 - r) = 200)
(h2 : a * (1 - r ^ 4022) / (1 - r) = 380) :
a * (1 - r ^ 6033) / (1 - r) = 542 := by
  -- some basic first: r≠1 (technicaly the formalization could be called incorrect but seems more of a formality)
  have hr1 : r ≠ 1 := by
    intro hr; rw [hr] at h1; norm_num at h1
  -- we can cleverly combine the terms
  have h3:=
    calc (a * (1 - r ^ 2011) / (1 - r))^2 - (a * (1 - r ^ 2011) / (1 - r))*(a * (1 - r ^ 4022) / (1 - r)) + (a * (1 - r ^ 4022) / (1 - r))^2
    _ = a^2 / ((1 - r)^2) * ((1 - r ^ 2011)^2 - (1 - r ^ 2011)*(1 - r ^ 4022) + (1 - r ^ 4022)^2) := by ring_nf; norm_num; ring_nf;
    _ = a^2 / ((1 - r)^2) * (1 - 2*r^2011 + r^4022 - 1 + r^2011 + r^4022 - r^6033 + 1 - 2*r^4022 + r^8044) := by ring_nf
    _ = a^2 / ((1 - r)^2) * (1 - r^2011 - r^6033 + r^8044) := by ring_nf
    _ = a^2 / ((1 - r)^2) * ((1-r^2011)*(1-r^6033)) := by ring_nf
    _ = a * (1-r^2011)/(1-r) * a * (1-r^6033)/(1-r) := by ring_nf; norm_num; ring_nf
  rw [h1, h2] at h3; norm_num at h3
  -- now that we have the r^6033 term we are almost done
  apply congr_arg (fun x=> 1/200 * x) at h3
  ring_nf at h3;
  rw [h3]
  ring_nf