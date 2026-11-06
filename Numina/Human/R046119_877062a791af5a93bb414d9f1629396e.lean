import Mathlib

/- What is the greatest integer value of $x$ such that $\frac{x^2 + 2x + 5}{x-3}$ is an integer?-/
theorem algebra_14437 : IsGreatest {x : ℤ | x - 3 ≠ 0 ∧ ∃ k : ℤ, (x ^ 2 + 2 * x + 5) / (x - 3 : ℚ) = k} 23 := by
  constructor
  -- Verify that x=23 is a solution.
  . norm_num
    use 29
    rfl
  -- Prove that 23 is the greatest.
  intro x ⟨hxne, ⟨k, hk⟩⟩
  have : (x : ℚ) - 3 ≠ 0 := by exact_mod_cast hxne
  field_simp at hk
  -- Since $(x^2+2x+5)/(x-3)$ is an integer, it's clear that $x-3$ divides $x^2+2x+5$.
  have hxdvd : x - 3 ∣ x ^ 2 + 2 * x + 5 := by
    use k
    qify
    linear_combination hk
  -- Notice that $x^2+2x+5=(x-3)(x+5)+20$,
  rw [show x ^ 2 + 2 * x + 5 = (x - 3) * (x + 5) + 20 by ring] at hxdvd
  -- we have $x-3$ divides 20.
  replace hxdvd := hxdvd.sub (Int.dvd_mul_right (x - 3) (x + 5))
  rw [add_sub_cancel_left] at hxdvd
  -- Hence $x-3$ is less than or equal 20.
  replace hxdvd := Int.le_of_dvd (by norm_num) hxdvd
  -- Finally, we draw a conclusion that x=23 is the greatest solution.
  linarith
