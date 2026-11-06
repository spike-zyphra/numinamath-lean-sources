import Mathlib
/- Find the maximum value of the expression x ^ 2 + y ^ 2 + z ^ 2, if x, y, z are integrals satisfying the system xy+x+y=20, yz+z+y=6,xz+x+z=2 
-/
theorem algebra_178148 :
    IsGreatest {t : ℤ | ∃ x y z, t = x^2 + y^2 + z^2 ∧ x * y + x + y = 20 ∧ y * z + z + y = 6 ∧ x * z + x + z = 2} 84 := by 
  constructor
  · -- Show that 84 is in the set
    use -4, -8, -2
    norm_num
  · -- Show that 84 is an upper bound
    intro t
    rintro ⟨x, y, z, h_eq, h1, h2, h3⟩
    -- we factor the equations to simplify the problem --
    have h4 : (x + 1) * (y + 1) = 21 := by
      nlinarith
    have h5 : (y + 1) * (z + 1) = 7 := by
      nlinarith
    have h6 : (x + 1) * (z + 1) = 3 := by
      nlinarith
    -- Then we use dvd relation to find the possible values of x, y, z --
    have h7 : (y + 1) ∣ 7 := by
      have : (y + 1) ∣ 7 := ⟨z + 1, by rw [h5]⟩
      exact this
    have : y + 1 = 1 ∨ y + 1 = -1 ∨ y + 1 = 7 ∨ y + 1 = -7 := by
      have h8 : (y + 1) ≠ 0 := by
        by_contra h
        rw [h] at h5
        omega
      -- to avoid the negative case, we consider the square of y + 1 --
      have h9 : (y + 1) ^ 2 ∣ 49 := by
        exact pow_dvd_pow_of_dvd h7 2
      have h11 : (y + 1) ^ 2 ≤ 49 := by
          exact Int.le_of_dvd (by norm_num) h9
      have h14 : y + 1 ≤ 7 := by nlinarith [sq_nonneg (y + 1), h11]
      have h15 : y + 1 ≥ -7 := by nlinarith [sq_nonneg (y + 1), h11]
      have h16 : (y + 1) = 1 ∨ (y + 1) = -1 ∨ (y + 1) = 7 ∨ (y + 1) = -7 := by
        interval_cases h : (y + 1) <;> tauto
      exact h16
     -- discuss all cases of y, just plug y into hx,hz --
    rcases this with (h71 | h72 | h73 | h74)
    · -- Case y + 1 = 1
      have hy : y = 0 := by linarith
      have hz : z = 6 := by
        rw [h71] at h5
        have hz1 : (z + 1) = 7 := by
          omega
        linarith
      rw [hz] at h6
      have : (x + 1) * 7 = 3 := by omega
      omega
    · -- Case y + 1 = -1
      have hy : y = -2 := by linarith
      have hz : z = -8 := by
        rw [h72] at h5
        have hz1 : (z + 1) = -7 := by
          omega
        linarith
      rw [hz] at h6
      have : (x + 1) * (-7) = 3 := by omega
      omega
    · -- Case y + 1 = 7
      have hy : y = 6 := by linarith
      have hz : z = 0 := by
        rw [h73] at h5
        have hz1 : (z + 1) = 1 := by
          omega
        linarith
      rw [hz] at h6
      have hx : x = 2 := by
        have : (x + 1) = 3 := by
          omega
        linarith
      simp [hx,hy,hz,h_eq]
    · -- Case y + 1 = -7
      have hy : y = -8 := by linarith
      have hz : z = -2 := by
        rw [h74] at h5
        have hz1 : (z + 1) = -1 := by
          omega
        linarith
      rw [hz] at h6
      have hx : x = -4 := by
        have : (x + 1) = -3 := by
          omega
        linarith
      simp [hx,hy,hz,h_eq]