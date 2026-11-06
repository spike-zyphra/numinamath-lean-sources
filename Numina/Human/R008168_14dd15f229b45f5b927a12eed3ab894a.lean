import Mathlib

/- Trouver tous les entiers $x, y \geqslant 1$ tels que

$$
\frac{1}{x}+\frac{1}{y}=\frac{1}{2017}
$$ -/
theorem number_theory_607725 :
  {(x, y) : ℕ × ℕ | x ≥ 1 ∧ y ≥ 1 ∧ (1 : ℚ) / x + 1 / y = 1 / 2017} =
    {(4034, 4034), (2017 * 2018, 2018), (2018, 2017 * 2018)} := by
  ext ⟨x, y⟩
  simp
  constructor
  -- First, we verify that the elements of the set are in the set
  swap
  . rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals
      norm_num
  -- Let 1 / x + 1 / y = 1 / 2017
  . rintro ⟨hx₀, hy₀, h⟩
    -- We have 2017 ≤ x, y
    have hx : 2017 ≤ x := by
      have hx : (x : ℚ)⁻¹ ≤ 2017⁻¹ := by
        linarith [show (y : ℚ)⁻¹ ≥ 0 by positivity]
      rw [inv_le_inv₀ (by norm_cast) (by norm_num)] at hx
      norm_cast at hx
    have hy : 2017 ≤ y := by
      have hy : (y : ℚ)⁻¹ ≤ 2017⁻¹ := by
        linarith [show (x : ℚ)⁻¹ ≥ 0 by positivity]
      rw [inv_le_inv₀ (by norm_cast) (by norm_num)] at hy
      norm_cast at hy
    -- Cancel the denominators
    field_simp at h
    -- We get (x - 2017) * (y - 2017) = 2017 ^ 2
    replace h : ((x : ℚ) - 2017) * ((y : ℚ) - 2017) = 2017 ^ 2 := by linear_combination -h
    -- Cast it back to ℕ
    replace h : (x - 2017) * (y - 2017) = 2017 ^ 2 := by
      qify
      simpa [hx, hy]
    -- Three cases : x - 2017 = 1, y - 2017 = 1, or x - 2017 = y - 2017 = 2017
    by_cases hx' : x - 2017 = 1
    {
      rw [hx'] at h
      simp at h
      omega
    }
    by_cases hy' : y - 2017 = 1
    {
      rw [hy'] at h
      simp at h
      omega
    }
    rw [Nat.Prime.mul_eq_prime_sq_iff (show Nat.Prime 2017 by norm_num) hx' hy'] at h
    omega
