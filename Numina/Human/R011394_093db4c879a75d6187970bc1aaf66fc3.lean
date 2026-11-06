import Mathlib

/- Find all triplets of three strictly positive integers such that:

$$
x+\frac{1}{y+\frac{1}{z}}=\frac{10}{7}
$$ -/
theorem algebra_109540 :
    { (x, y, z) : ℕ × ℕ × ℕ | x > 0 ∧ y > 0 ∧ z > 0 ∧ x + 1 / (y + 1 / z : ℚ) = 10 / 7 } = { (1, 2, 3) } := by
  ext ⟨x, y, z⟩
  simp
  constructor
  -- We first verify that `x = 1` and `y = 2` and `z = 3` is a solution.
  swap
  . rintro ⟨rfl, rfl, rfl⟩
    norm_num
  -- If `x + 1 / (y + 1 / z) = 10 / 7`
  . rintro ⟨hx, hy, hz, h⟩
    -- `1 / (y + 1 / z)` is between `0`(inclusive) and `1`(exclusive)
    have h₁ : 0 ≤ (y + (z : ℚ)⁻¹)⁻¹ := by positivity
    have h₂ : (y + (z : ℚ)⁻¹)⁻¹ < 1 := by
      refine inv_lt_one_of_one_lt₀ ?_
      have h₂ : 1 ≤ (y : ℚ) := Nat.one_le_cast.mpr hy
      have h₃ : 0 < (z : ℚ)⁻¹ := by positivity
      linarith
    -- Apply `Int.floor` to both sides of the equation
    have h₃ := congrArg Int.floor h
    -- We have `⌊x + (y + (z : ℚ)⁻¹)⁻¹⌋ = x`
    have h₄ : ⌊x + (y + (z : ℚ)⁻¹)⁻¹⌋ = x := by
      rw [Int.floor_eq_iff]
      simp [h₁, h₂]
    -- So `x = 1`.
    norm_num [h₄] at h₃
    subst x
    clear hx h₁ h₂ h₄
    -- We have `(y + (z : ℚ)⁻¹)⁻¹ = (7 / 3)⁻¹`
    replace h : (y + (z : ℚ)⁻¹)⁻¹ = (7 / 3)⁻¹ := by
      linarith only [h]
    -- So `y + (z : ℚ)⁻¹ = 7 / 3`
    rw [inv_inj] at h
    -- Since `0 < z⁻¹` and `z⁻¹ ≤ 1`, we have `1 < y < 3`.
    have h₁ : 0 < (z : ℚ)⁻¹ := by positivity
    have h₂ : (z : ℚ)⁻¹ ≤ 1 := Nat.cast_inv_le_one z
    have h₃ : 1 < (y : ℚ) := by linarith
    have h₄ : (y : ℚ) < 3 := by linarith
    -- So `y = 2`.
    norm_cast at h₃ h₄
    obtain rfl : y = 2 := by omega
    -- The rest is trivial.
    replace h : (z : ℚ)⁻¹ = 3⁻¹ := by
      linarith only [h]
    rw [inv_inj] at h
    norm_cast at h
