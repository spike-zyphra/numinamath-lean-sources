import Mathlib

theorem algebra_16227 :
  IsGreatest { n | n > 0 ∧ ∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧
      n^2 = x^2 + y^2 + z^2 + 2 * x * y + 2 * y * z + 2 * z * x + 3 * x + 3 * y + 3 * z - 6 } 8 := by
  constructor
  · -- Show that 8 is in the set
    constructor
    · norm_num
    · -- Show existence of positive integers x, y, z such that 8^2 = x^2+y^2+z^2+2xy+2yz+2zx+3x+3y+3z-6
      use 1, 1, 5
      all_goals norm_num
  · -- Show that 8 is greatest
    intro n hn
    rcases hn with ⟨hn_pos, x, y, z, hx, hy, hz, h_eq⟩
    by_contra h
    push_neg at h
    -- Assume n > 8, so n ≥ 9
    have h1 : n ≥ 9 := by omega
    -- The equation simplifies to n^2 = (x+y+z)^2 + 3(x+y+z) - 6
    -- Let k = x+y+z. Then, n^2 = k^2 + 3k - 6
    -- Multiply by 4: 4n^2 = 4k^2 + 12k - 24
    -- Rearrange to get: 4k^2 + 12k - 24 - 4n^2 = 0
    -- Then: (2k + 3)^2 - (2n)^2 = 33
    -- This is a difference of squares: (2k + 3 - 2n)(2k + 3 + 2n) = 33
    have eq1 : (2 * (x + y + z) + 3 : ℤ) ^ 2 - (2 * n : ℤ) ^ 2 = 33 := by
      nlinarith
    -- Factor the difference of squares
    have eq2 : (2 * (x + y + z) + 3 - 2 * n : ℤ) * (2 * (x + y + z) + 3 + 2 * n : ℤ) = 33 := by
      nlinarith [eq1]
    -- Now we need to find the possible integer solutions. We have to analyze the divisors of 33.
    have h2 : (2 * (x + y + z) + 3 - 2 * n : ℤ) ∣ 33 := by
      use (2 * (x + y + z) + 3 + 2 * n : ℤ)
      all_goals linarith
    -- The possible integer values are bounded. We now need to proceed with case analysis to check the possible integer divisors.
    have h3 : (2 * (x + y + z) + 3 - 2 * n : ℤ) ≤ 33 := by
      apply Int.le_of_dvd (by norm_num) h2
    have h4 : (2 * (x + y + z) + 3 - 2 * n : ℤ) ≥ -33 := by
      have h5 : (- (2 * (x + y + z) + 3 - 2 * n) : ℤ) ∣ 33 := by
        exact Int.neg_dvd.2 h2
      have h6 : (- (2 * (x + y + z) + 3 - 2 * n) : ℤ) ≤ 33 := by
        apply Int.le_of_dvd (by norm_num) h5
      omega
    interval_cases h5 : (2 * (x + y + z) + 3 - 2 * n : ℤ) <;> omega