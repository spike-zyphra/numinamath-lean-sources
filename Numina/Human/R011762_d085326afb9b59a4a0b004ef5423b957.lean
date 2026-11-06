import Mathlib

/- 9.3. Natural numbers $a, x$ and $y$, greater than 100, are such that $y^{2}-1=$ $=a^{2}\left(x^{2}-1\right)$. What is the smallest value that the fraction $a / x$ can take? -/
theorem number_theory_154971 :
    IsLeast {r : ℚ | ∃ a x y : ℤ, a > 100 ∧ x > 100 ∧ y > 100 ∧ y^2 - 1 = a^2 * (x^2 - 1) ∧ r = a / x} (2) := by
  unfold IsLeast
  constructor
  · -- Show that 2 is attained
    simp
    -- Use the solution (a, x, y) = (202, 101, 20401)
    use 202
    simp
    use 101
    simp
    use 20401
    simp
    norm_num
  -- Show that 2 is a lower bound
  rw [mem_lowerBounds]
  simp
  intro r a ha x hx y hy h hr
  subst r
  -- Rewrite to have difference of squares
  have diff_sq : (a * x - y) * (a * x + y) = a ^ 2 - 1 := by linarith
  let k := a * x - y
  -- Show that a * x + y and a ^ 2 - 1 are positive
  have : 0 < a * x + y ∧ 0 < a ^ 2 - 1 := ⟨by positivity, by rw [lt_sub_iff_add_lt']; nlinarith⟩
  rw [← diff_sq] at this
  -- k is positive
  have k_pos : 0 < k := pos_of_mul_pos_left this.2 (by linarith)
  -- We will need these divisiblity claims later
  have k_dvd : k ∣ a ^ 2 - 1 := dvd_of_mul_right_eq (a * x + y) diff_sq
  have k_dvd'' : k ∣ (k - a ^ 2 + 1) := by
    rcases k_dvd with ⟨u, hu⟩
    use (1 - u)
    linarith
  have k_dvd' : k ∣ (k - 1) * (k - a ^ 2 + 1) := by
    rcases k_dvd with ⟨u, hu⟩
    use (k - 1) * (1 - u)
    rw [show k - a ^ 2 + 1 = k * (1 - u) by linarith]
    linarith
  have h' : a * x + y = (a ^ 2 - 1) / k := by unfold k; exact (Int.ediv_eq_of_eq_mul_right (by positivity) diff_sq.symm).symm
  have : a * x - y = k := by rfl
  -- Add this and h' together
  have eqn : 2 * a * x = (a ^ 2 - 1) / k + k := by linear_combination this + h'
  have eqn2 : (a ^ 2 - 1) / k + k = a ^ 2 + (k - 1) * (k - a ^ 2 + 1) / k := by
    rw [← Int.mul_eq_mul_left_iff (show k ≠ 0 by positivity), mul_add, mul_add]
    rw [← Int.mul_ediv_assoc k k_dvd, Int.mul_ediv_cancel_left (a ^ 2 - 1) (show k ≠ 0 by positivity)]
    rw [← Int.mul_ediv_assoc k k_dvd', Int.mul_ediv_cancel_left _ (show k ≠ 0 by positivity)]
    ring
  rw [eqn2] at eqn
  -- Bring it all together
  have ineq : 2 * a * x ≤ a ^ 2 := by
    calc
      2 * a * x = a ^ 2 + (k - 1) * (k - a ^ 2 + 1) / k := by tauto
      _ ≤ a ^ 2 := by
        -- Prove that the second term is negative
        have : 0 ≤ k - 1 := by linarith
        have nonpos : k - a ^ 2 + 1 ≤ 0 := by
          have : k ≤ a ^ 2 - 1 := Int.le_of_dvd (by rw [lt_sub_iff_add_lt']; nlinarith) k_dvd
          linarith
        have : (k - a ^ 2 + 1) / k ≤ 0 := Int.ediv_le_of_le_mul (by positivity) (by simp [nonpos])
        have : (k - 1) * (k - a ^ 2 + 1) / k ≤ 0 := by
          rw [Int.mul_ediv_assoc (k - 1) k_dvd'']
          rw [mul_nonpos_iff]
          left
          tauto
        linarith
  -- Multiply by a * x and finish
  rw [← mul_le_mul_left (show (0 : ℚ) < a * x by positivity), mul_assoc (a : ℚ) x (a / x), mul_div_cancel₀ (a : ℚ) (by positivity)]
  qify at ineq
  linarith