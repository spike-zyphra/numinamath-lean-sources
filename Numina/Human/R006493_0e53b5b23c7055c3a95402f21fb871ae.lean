import Mathlib

-- Let k be a positive integer. The lengths of the sides of a triangle are integers, its area is also an integer, one side has length 6k^2−3 and its perimeter is 12k^2. Show that the length of the shortest side of such a triangle is 6k^2−3 if k=1, and 2k^2+2 if k≥2.
theorem number_theorem_637668 : ∀ k > 0,∃ (a b c:ℤ), a = 6*k^2-3 ∧ a + b + c = 12*k^2 ∧ ∃ m, (6*k^2*(6*k^2-a)*(6*k^2-b)*(6*k^2-c)=m^2) ∧ min (min a b) c = if k = 1 then 6 * k^2 - 3 else 2 * k^2 + 2 := by
  intro k hk
  -- Split into k = 1 and k ≥ 2 cases
  by_cases hkone : k = 1
  -- Case k = 1: use (3, 4, 5)
  · use 3, 4, 5
    rw [hkone]; simp
    use 6; simp
  -- Case k ≥ 2: use (6k^2-3, 2k^2+2, 4k^2+1)
  · use 6*k^2-3, 2*k^2+2, 4*k^2+1
    simp; constructor
    · ring
    · constructor
      · use 6*k*(2*k^2-1); ring
      · have : min (min (6 * k ^ 2 - 3) (2 * k ^ 2 + 2)) (4 * k ^ 2 + 1) = 2*k^2+2 := by
          have : min (6 * k ^ 2 - 3) (2 * k ^ 2 + 2) = (2 * k ^ 2 + 2) := by
            apply Int.min_eq_right
            have : k ^ 2 ≥ 2 := by
              have : k ≥ 2 := by omega
              nlinarith
            linarith
          rw [this]
          apply Int.min_eq_left
          nlinarith
        rw [this]
        exact Eq.symm (if_neg hkone)
