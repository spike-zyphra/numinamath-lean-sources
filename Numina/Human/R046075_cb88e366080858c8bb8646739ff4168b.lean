import Mathlib
/-Montasser creates a sequence of numbers. The first two numbers are 6 and 15. He generates each subsequent number in the sequence by dividing the last number by the one before it and then multiplying the result by 2. Thus, the third number in the sequence is 15/6 * 2 =5
and the fourth number is 5/15 * 2 =2/3
What is the hundredth number in the sequence?-/
theorem algebra_174218 (a : ℕ → ℚ) (ha0 : a 0 = 6) (ha1 : a 1 = 15)
    (han : ∀ n, a (n + 2) = 2 * (a (n + 1)) / (a n)) :
    a 99 = 2 / 3 := by
   -- we first compute a1 - a7
  have a2 : a 2 = 5 := by
    rw [han 0, ha0, ha1]
    norm_num
  have a3 : a 3 = 2 / 3 := by
    rw [han 1, ha1, a2]
    norm_num
  have a4 : a 4 = 4 / 15 := by
    rw [han 2, a2, a3]
    norm_num
  have a5 : a 5 = 4 / 5 := by
    rw [han 3, a3, a4]
    norm_num
  have a6 : a 6 = 6 := by
    rw [han 4, a4, a5]
    norm_num
  have a7 : a 7 = 15 := by
    rw [han 5, a5, a6]
    norm_num
  -- then we prove that an is cyclic with period 6 using strong induction
  have f: ∀ n, a (n + 6) = a n := by
    intro n
    induction' n using Nat.strongRecOn with n ih
    by_cases l: n = 0
    -- case n = 0
    . simp [l,a6,ha0]
    . by_cases o: n = 1
      -- case n = 1
      . simp [o,a7,ha1]
      -- case 2 ≤ n
      . have hn: 2 ≤ n := by omega
        have o1: 0 < n := by omega
        have o2: n - 2 < n := by omega
        clear l o
        have g1:= ih (n - 1)
        simp [o1] at g1
        rw [show n - 1 + 6 = n + 5 by omega] at g1
        have g2:= ih (n - 2)
        rw [show n - 2 + 6 = n + 4 by omega] at g2
        simp [o2] at g2
        have f1:= han (n + 4)
        simp [f1]
        rw [show n + 4 + 1 = n + 5 by omega]
        simp [g1,g2]
        have f2:= han (n - 2)
        rw [show n - 2 + 2 = n by omega] at f2
        rw [show n - 2 + 1 = n - 1 by omega] at f2
        simp [f2]
  -- then we use f to compute a(6k+3)
  have f_mod_3: ∀ k, a (6 * k + 3) = 2 / 3 := by
    intro k
    induction' k with k ih
    . simp [a3]
    . rw [show 6 * (k + 1) + 3 = 6 * k + 3 + 6 by omega]
      specialize f (6 * k + 3)
      rw [f]
      exact ih
  -- then we use f_mod_3 to compute a(99)
  specialize f_mod_3 16
  rw [show 6 * 16 + 3 = 99 by omega] at f_mod_3
  exact f_mod_3
  