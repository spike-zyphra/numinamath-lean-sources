import Mathlib

theorem algebra_100755 (A B C D a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (hf : ∀ x, f x = A * x ^ 3 + B * x ^ 2 + C * x + D)
    (h : ∫ x in (-a)..a, f x = 0) :
    B * a ^ 2 + 3 * D = 0 := by
  have h1 : ∫ x in (-a)..a, f x = ∫ x in (-a)..a, (A * x ^ 3 + B * x ^ 2 + C * x + D) := by
    congr
    funext x
    exact hf x
  rw [h1] at h
  have h2 : ∫ x in (-a)..a, (A * x ^ 3 + B * x ^ 2 + C * x + D) =
      B * (2 * a^3 / 3) + 2 * a * D := by
    simp [intervalIntegral.integral_const, add_mul, mul_add, mul_comm A, mul_comm B, mul_comm C, mul_assoc]
    <;> ring_nf
    <;> field_simp
    <;> ring
  rw [h2] at h
  have ha2 : a ≠ 0 := by linarith
  have h3 : B * (2 * a^3 / 3) + 2 * a * D = 0 := by linarith
  have h4 : B * a ^ 3 + 3 * a * D = 0 := by
    nlinarith
  have h5 : a * (B * a ^ 2 + 3 * D) = 0 := by
    linarith [h4]
  cases' (mul_eq_zero.mp h5) with ha6 ha7
  · -- Since a > 0 we have a contradiction.
    linarith [ha]
  · -- The second case gives us the required relation.
    linarith [ha7]