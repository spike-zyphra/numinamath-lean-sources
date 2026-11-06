import Mathlib

/- 12.44 Find the natural number solutions $x, y$ for the equation $x^{3}-y^{3}=x y+61$.
(15th All-Soviet Union Mathematical Olympiad, 1981) -/
theorem number_theory_279007 {x y : ℕ} (h : x^3 - y^3 = x * y + 61) :
    x = 6 ∧ y = 5 := by
  -- prove that x = y + d for some positive d
  have ⟨d, hd, hx⟩ : ∃ d > 0, x = y + d := by
    -- it is enough to show that x > y
    suffices x > y by use x - y; omega
    -- suppose that x ≤ y and show that x^3 - y^3 ≠ x * y + 61 in this case
    contrapose! h
    have : x ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left h _
    rw [Nat.sub_eq_zero_of_le this]
    omega
  have h3 : y ^ 3 < x ^ 3 := by
    rw [hx]
    apply Nat.pow_lt_pow_left (by omega) (by norm_num)
  zify [h3] at h
  rw [hx] at h ⊢
  push_cast at h
  -- we get the following equality:
  -- d^3 = 61 - ((3 * d - 1) * y^2 + d * (3 * d - 1) * y)
  -- it follows that d^3 ≤ 61
  have hd3 : (d : ℤ) ^ 3 ≤ 61 := calc
    (d : ℤ) ^ 3 = 61 - ((3 * d - 1) * y ^ 2 + d * (3 * d - 1) * y) := by linear_combination h
    _     ≤ 61 - 0 := by
      apply sub_le_sub (le_refl _)
      apply add_nonneg <;> apply mul_nonneg <;> nlinarith
  norm_cast at hd3
  -- d^3 ≤ 61 and 0 < d imply that d = 1, 2, or 3
  have : d ≤ 3 := by
    contrapose! hd3
    apply lt_of_lt_of_le (show 61 < 4 ^ 3 by norm_num)
    apply Nat.pow_le_pow_left (by omega)
  interval_cases d <;> clear * - h
  -- if d = 1 then we get 2 * (y - 5) * (y + 6) = 0
  -- so y = 5
  · have eq : 2 * ((y : ℤ) - 5) * (y + 6) = 0 := by linear_combination h
    simp_rw [mul_eq_zero] at eq
    omega
  -- if d = 2 then we get 5 * y^2 + 10 * y = 53
  -- this equation has no natural solutions
  · have eq : 5 * (y : ℤ) ^ 2 + 10 * y = 53 := by linear_combination h
    omega
  -- if d = 3 then we get 8 * y^2 + 24 * y = 34
  -- this equation has no natural solutions
  · have eq : 8 * (y : ℤ) ^ 2 + 24 * y = 34 := by linear_combination h
    omega