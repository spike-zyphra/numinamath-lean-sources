import Mathlib

theorem algebra_12650 (z : ℂ) (hz : z^4 + z^3 + z^2 + z + 1 = 0) : z^2015 = 1 := by 
  have h1 : z ≠ 0 := by
    by_contra h
    rw [h] at hz
    norm_num at hz
  have h2 : z^5 = 1 := by
    have eq1 : z^5 - 1 = 0 := by
      have eq2 : z^4 + z^3 + z^2 + z + 1 = 0 := hz
      have eq3 : (z - 1) * (z^4 + z^3 + z^2 + z + 1) = 0 := by
        rw [eq2]
        norm_num
      have eq4 : (z - 1) * (z^4 + z^3 + z^2 + z + 1) = z^5 - 1 := by
        ring
      rw [eq4] at eq3
      exact_mod_cast eq3
    have eq6 : z^5 = 1 := by
      have h : z^5 - 1 = 0 := eq1
      have : z^5 = 1 := by
        calc
          z^5 = (z^5 - 1) + 1 := by ring_nf
          _ = 0 + 1 := by rw [h]
          _ = 1 := by ring
      exact_mod_cast this
    exact_mod_cast eq6
  have h3 : z^2015 = (z^5)^403 := by
    calc
      z^2015 = z^(5 * 403) := by norm_num
      _ = (z^5)^403 := by rw [pow_mul]
  rw [h3, h2]
  all_goals norm_num