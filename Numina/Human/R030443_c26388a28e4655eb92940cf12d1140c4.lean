import Mathlib

open Finset

/- Problem 3. Let the number $S=1+3^{3}+3^{6}+3^{9}+\ldots+3^{2010}$.

a) Show that the number $26 S+1$ is a perfect cube.

b) Determine the natural number $a$ for which the equality $a^{61}=26 S+1$ holds.

Nicolae Bivol, Corabia -/
theorem number_theory_114480 {S : ℕ} (hS : S = ∑ i ∈ range 671, 3^(3*i)) :
    (∃ m, m^3 = 26 * S + 1) ∧ (3 ^ 33)^61 = 26 * S + 1 := by
  -- first we write S as a geometric sum and use it's formula as a real number
  replace hS : S = ∑ i ∈ range 671, 27^i := by
    rw [hS]
    congr
    ext i
    rw [pow_mul]
    ring
  replace hS : (S : ℝ) = ∑ i ∈ range 671, (↑(27:ℕ) : ℝ)^i := by
    rw [hS]
    push_cast
    rfl
  rw [geom_sum_eq (by norm_num)] at hS
  -- now using the fomula we write 26 * s + 1 = 27^671
  have : 26 * S + 1 = 27 ^ 671 := by
    rify
    rw [hS]
    ring
  rw [this]
  -- now we can prove the goals, using 3^671 as m
  and_intros
  . use 3 ^ 671
    rw [← pow_mul, mul_comm, pow_mul]
    congr
  . rw [show 27 = 3 ^ 3 by norm_num]
    rw [← pow_mul, ← pow_mul]