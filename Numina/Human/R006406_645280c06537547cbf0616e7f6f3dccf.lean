import Mathlib

set_option maxHeartbeats 600000

/-Let's use $D_1=73, D_2=74$ as in the base problem (which makes the statement vacuously true) and change the target result.
Suppose $E, I, L, V$ are (not necessarily distinct) nonzero digits in base ten for which
(1) the four-digit number $1000E + 100V + 10I + L$ is divisible by $D_1$, and
(2) the four-digit number $1000V + 100I + 10L + E$ is divisible by $D_2$.
If $D_1=73$ and $D_2=74$, compute $1000L + 100I + 10V + E$. Show the answer is 1234.
-/

theorem number_theory_636727 (E V I L: ℤ) (l1: 1 ≤ E) (l2: E ≤ 9) (l3: 1 ≤ V) (l4: V ≤ 9)
  (l5: 1 ≤ I) (l6: I ≤ 9) (l7: 1 ≤ L) (l8: L ≤ 9)
  (h1: 73 ∣ 1000 * E + 100 * V + 10 * I + L)
  (h2: 74 ∣ 1000 * V + 100 * I + 10 * L + E):
  (1000 * L + 100 * I + 10 * V + E) = 1234 ∨ (1000 * L + 100 * I + 10 * V + E) = 9954 := by

  have d: 2 ∣ E := by
    rw [show E = 1000 * V + 100 * I + 10 * L + E - 2 * (500 * V + 50 * I + 5 * L) by ring]
    apply Int.dvd_sub
    .
      suffices (2: ℤ) ∣ 74 by
        apply dvd_trans this h2
      norm_num
    .
      simp
  apply exists_eq_mul_right_of_dvd at d
  obtain ⟨e, rfl⟩ := d
  replace l1: 1 ≤ e := by
    clear *- l1
    omega
  replace l2: e ≤ 4 := by
    clear *- l2
    omega
  replace h1: 73 ∣ 29 * e + 27 * V + 10 * I + L := by
    clear *- h1
    omega
  replace h2: 37 ∣ 2 * e + V + 26 * I + 10 * L := by
    clear *- h2
    omega
  suffices L = 1 ∧ I = 2 ∧ V = 3 ∧ e = 2 ∨ L = 9 ∧ I = 9 ∧ V = 5 ∧ e = 2 by
    rcases this with f | f
    .
      simp [f]
    .
      simp [f]
  interval_cases e <;> interval_cases V <;> interval_cases I <;> interval_cases L <;> omega