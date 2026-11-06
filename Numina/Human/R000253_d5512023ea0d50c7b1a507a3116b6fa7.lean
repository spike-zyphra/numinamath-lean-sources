import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- On the board is written in decimal the integer positive number  $N$ . If it is not a single digit number,
  wipe its last digit  $c$  and replace the number  $m$  that remains on the board with a number  $m -3c$ .
  (For example, if  $N = 1,204$  on the board,  $120 - 3 \cdot  4 = 108$ .) Find all the natural numbers  $N$ ,
  by repeating the adjustment described eventually we get the number  $0$ .-/
theorem number_theory_8710 :
  let f : ℤ → ℤ := fun n => n / 10 - 3 * (n % 10);
  -- All numbers that meet the conditions are multiples of 31.
  ∀ n, (∃ k, Nat.iterate f k n = 0) →   31 ∣ n := by
    intro f n h
    obtain ⟨k, hk⟩ := h
    revert n
    -- induction on the number of operations.
    induction' k using Nat.strong_induction_on with k ih
    by_cases k0 : k = 0
    · -- if `f^[0] n = 0`, $n = 0$. So $31 \mid n$.
      intro n hk; simp [k0] at hk; tauto
    · -- case $k \ne 0 :$
      -- `f^[k] n ` = `f^[k - 1] (f n)`. By assumption, $31 \mid (f n)$, implies $31 \mid n$.
      intro n hk
      rw [show k = k - 1 + 1 by exact Eq.symm (succ_pred_eq_of_ne_zero k0), Function.iterate_add] at hk
      simp at hk
      have h1 := ih (k - 1) (by simp; positivity) (f n) hk
      simp [f] at h1
      have : n = (n / 10 - 3 * (n % 10) ) * 10 + 31 * (n % 10) := by
        ring_nf
        exact Eq.symm (Int.ediv_add_emod' n 10)
      rw [this]
      exact Int.dvd_add (Dvd.dvd.mul_right h1 10) (Int.dvd_mul_right 31 (n % 10))
    