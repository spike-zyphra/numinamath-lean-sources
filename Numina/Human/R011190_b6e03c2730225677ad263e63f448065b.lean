import Mathlib

/-Each number in the sequence starting
2,3,6,8,8,4,… is obtained in the following way. The first two numbers are 2 and 3 and afterwards each number is the last digit of the product of the two preceding numbers in the sequence. What is the 2017th number in the sequence? A 8 B 6 C 4 D 3 E 2-/

def f (n : ℕ) : ℕ := match n with
| 0 => 2
| 1 => 3
| n + 2 => (f n) * (f (n + 1)) % 10

theorem number_theorem_229705: f 2016 = 2 := by

  -- we show that if we remove the first two terms, then f is periodic with length 6
  have h: ∀ n, 2 ≤ n → f (n + 6) = f n := by
    intro n
    induction' n using Nat.strongRec with n ih  --using strong induction
    intro hn
    by_cases l: n < 4
    -- base case
    .
      have o: n = 2 ∨ n = 3 := by omega
      rcases o with o | o
      .
        simp [o, f]
      .
        simp [o, f]
    -- induction step
    .
      replace l: 4 ≤ n := by omega
      clear hn
      set n':= n + 4
      have hn': n' = n + 4 := by omega
      rw [show n + 6 = n' + 2 by simp [n']]
      clear_value n'
      simp [f]
      simp [hn']
      have s1:= ih (n - 2)
      have o: n - 2 < n := by omega
      simp [o] at s1
      have t: 2 ≤ n - 2 := by omega
      simp [t] at s1
      clear o t
      rw [show n - 2 + 6 = n + 4 by omega] at s1
      rw [s1]
      clear s1
      have s2:= ih (n - 1)
      have o: n - 1 < n := by omega
      have t: 2 ≤ n - 1 := by omega
      simp [o, t] at s2
      clear o t
      rw [show n - 1 + 6 = n + 5 by omega] at s2
      rw [show n + 4 + 1 = n + 5 by omega]
      rw [s2]
      clear s2 ih
      set n':= n - 2
      rw [show n - 1 = n' + 1 by simp [n']; omega]
      rw [show n = n' + 2 by simp[n']; omega]
      clear_value n'
      symm
      simp [f]

  -- then we give can show f(6 * k + 6) = 2
  have g: ∀ k, f (6 * k + 6) = 2 := by
    intro k
    induction' k with k ih

    -- base case
    .
      simp [f]

    -- induction step
    .
      specialize h (6 * (k + 1))
      have o: 2 ≤ 6 * (k + 1) := by omega
      simp [o] at h
      rw [h]
      rw [show 6 * (k + 1) = 6 * k + 6 by omega]
      exact ih

  -- finally, we use g to give the result
  rw [show 2016 = 6 * 335 + 6 by norm_num]
  specialize g 335
  simp at h
  exact g
  