import Mathlib

/-There is a sequence of numbers:
1,3,8,22,60,164,448,⋯ where the first number is 1, the second number is 3,
and starting from the third number, each number is exactly twice the sum of the previous two numbers.
In this sequence, the remainder when the 2000th number is divided by 9 is ?-/

def f (n : ℕ) : ℕ := match n with
| 0 => 5
| 1 => 1
| 2 => 3
| n + 3 => 2 * (f (n + 1) + f (n + 2))

theorem number_theory_170213: f 2000 % 9 = 3 := by

  -- we show that f n % 9 is periodic with period 9 by strong induction
  have h: ∀ n, f (n + 9) % 9 = f n % 9 := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n = 0
    -- base case
    .
      simp [l]
      simp [f]
    .
      by_cases r: n = 1
      -- base case
      .
        simp [r, f]
      -- induction step
      .
        replace l: 2 ≤ n := by omega
        clear r
        have h1:= ih (n - 1)
        have o: n - 1 < n := by omega
        simp [o] at h1
        clear o
        have h2:= ih (n - 2)
        have o: n - 2 < n := by omega
        simp [o] at h2
        clear o
        rw [show n - 1 + 9 = n + 8 by omega] at h1
        rw [show n - 2 + 9 = n + 7 by omega] at h2
        set n':= n + 6
        rw [show n + 9 = n' + 3 by simp [n']]
        have o: f (n' + 3) = 2 * (f (n' + 2) + f (n' + 1)) := by
          clear_value n'
          simp [f]
          ring
        rw [o]
        simp [n']
        rw [show n + 6 + 1 = n + 7 by simp]
        rw [show n + 6 + 2 = n + 8 by simp]
        rw [Nat.mul_mod]
        rw [Nat.add_mod]
        rw [show 2 % 9 = 2 by norm_num]
        rw [h1, h2]
        by_cases r: n = 2
        .
          simp [r, f]
        .
          replace l: 3 ≤ n := by omega
          clear r
          set n' := n - 3
          rw [show n = n' + 3 by omega]
          have o: f (n' + 3) = 2 * (f (n' + 2) + f (n' + 1)) := by
            clear_value n'
            simp [f]
            ring
          rw [o]
          simp

  -- then use h, we can give the value of f (9 * k + 2)
  have h1: ∀ k, f (9 * k + 2) % 9 = 3 := by
    intro k
    induction' k with k ih
    -- base case
    .
      simp [f]

    -- induction step
    .
      rw [show 9 * (k + 1) + 2 = 9 * k + 2 + 9 by omega]
      specialize h (9 * k + 2)
      rw [h]
      exact ih


  -- finally, use h1 to get the result
  specialize h1 222
  norm_num at h1
  exact h1
  