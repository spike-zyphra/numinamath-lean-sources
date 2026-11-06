import Mathlib

theorem algebra_20826 (x : ℝ) (hx : x ≠ 0) :
    (4 / x : ℝ)^(-1 : ℤ) * (3 * x^3 / x)^2 * (1 / (2 * x))^(-3 : ℤ) = 18 * x^8 := by 
  have h1 : (4 / x : ℝ) ^ (-1 : ℤ) = x / 4 := by
    simp [zpow_neg_one, hx]
    <;> field_simp [hx]
    <;> ring

  have h2 : (3 * x^3 / x : ℝ) ^ 2 = 9 * x^4 := by
    have h2a : (3 * x^3 / x : ℝ) = 3 * x^2 := by
      field_simp [hx]
      <;> ring
    rw [h2a]
    ring_nf

  have h3 : (1 / (2 * x) : ℝ) ^ (-3 : ℤ) = (2 * x) ^ 3 := by
    rw [zpow_neg, zpow_ofNat]
    field_simp [hx]
    <;> ring

  rw [h1, h2, h3]
  <;> ring_nf
  <;> field_simp [hx]
  <;> ring