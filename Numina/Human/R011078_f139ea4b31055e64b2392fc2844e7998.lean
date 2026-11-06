import Mathlib


/-4. The number of integer solutions $(x, y)$ for the equation $\frac{1}{x}+\frac{1}{y}=\frac{1}{7}$ is $(\mathrm{x})$.
A. 5
B. 6
C. 7
D. 8-/
theorem algebra_220023 : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) +
    (1 / y : ℚ) = 1 / 7}.ncard = 5 := by
-- It suffices to write out the solution set explicitly
  suffices : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) +
  (1 / y : ℚ) = 1 / 7} = ({(-42, 6), (6, -42), (8, 56), (56, 8), (14, 14)} : Finset (ℤ × ℤ))
  · rw [this]; norm_cast
  simp [Set.ext_iff]; intro x y; constructor
  -- Assume w. l. o. g. that $x$ is at most $y$
  · rintro ⟨xne, yne, heq⟩; wlog xley: x ≤ y
    · specialize this y x yne xne (by rw [← heq, add_comm]) (by omega)
      omega
    field_simp at heq; norm_cast at heq
    symm at heq; rw [← sub_eq_zero, ← add_left_inj 49] at heq
    rw [show x*y-(y+x)*7+49 = (x-7)*(y-7) by ring, zero_add] at heq
  -- Show that the absolute value of $x-7$ is a divisor of $49$
    have : (x - 7).natAbs ∈ Nat.divisors 49 := by
      simp; rw [show 49 = (49:ℤ).natAbs by rfl, Int.natAbs_dvd_natAbs]
      use y - 7; rw [heq]
    simp [show Nat.divisors 49 = {1, 7, 49} by decide] at this
    zify at this; repeat rw [abs_eq] at this
    repeat rw [or_assoc] at this
  -- Discuss all possible values of $x$, the goal will follow
    rcases this with h|h|h|h|h|h
    any_goals rw [h] at heq; omega
    all_goals norm_num
-- Conversely, it is straightforward to check that when $x$, $y$ are the given values, the equation holds true
  intro h; rcases h with ⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩
  all_goals norm_num [hx, hy]