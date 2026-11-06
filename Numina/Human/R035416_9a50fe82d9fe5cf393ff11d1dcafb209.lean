import Mathlib

/- 1. Determine all values of the natural number $n$ for which the system

$$
\left\{\begin{array}{l}
x+y=n^{2} \\
10 x+y=n^{3}
\end{array}\right.
$$

has a solution in the set of natural numbers. -/
theorem number_theory_251614: {n: ℤ | 0 ≤ n ∧ ∃ x y: ℤ, (0 ≤ x ∧ 0 ≤ y ∧ x + y = n ^ 2 ∧ 10 * x + y = n ^ 3)}
  = {0, 1, 3, 6 ,9, 10} := by

  ext n
  constructor

  -- the forward direction
  . intro h
    simp at h
    rcases h with ⟨hn, h⟩
    rcases h with ⟨x, hx, y, hy, h1, h2⟩
    simp
    replace h2: 9 * x = n ^ 2 * (n - 1) := by nlinarith
    by_cases d: 3 ∣ n

    -- case 1: 3 ∣ n
    . apply exists_eq_mul_right_of_dvd at d
      obtain ⟨k, hk⟩ := d
      have lk: 0 ≤ k := by
        omega
      simp [hk] at h2
      replace h2: x = k ^ 2 * (3 * k - 1) := by nlinarith
      replace h1: y = n ^ 2 - x := by omega
      simp [h2,hk] at h1
      replace h1: y = k ^ 2 * (10 - 3 * k) := by nlinarith
      have o: 0 ≤ 10 - 3 * k := by nlinarith
      replace o: k ≤ 3 := by omega
      interval_cases k
      all_goals simp [hk]

    -- case 2: 3 ∤ n, then 9 ∣ n - 1
    . have pp: IsCoprime 9 (n ^ 2):= by  -- we first show that 9 and n ^ 2 are coprime
        have o1: IsCoprime (3: ℤ) (n ^ 2) := by
          have o2: IsCoprime (3: ℤ) n := by
            rw [Int.isCoprime_iff_gcd_eq_one]
            rw [Int.gcd_eq_natAbs]
            set d:= Nat.gcd 3 n.natAbs with hd
            have s: d ∣ 3 := by
              simp [hd]
              apply Nat.gcd_dvd_left
            have o: d = 1 ∨ d = 3 := by
              apply Nat.Prime.eq_one_or_self_of_dvd
              norm_num
              exact s
            rcases o with o | o
            . exact o
            . have u: 3 ∣ n.natAbs := by
                rw [← o]
                simp [d]
                apply Nat.gcd_dvd_right
              rw [show (3: ℕ) = (3: ℤ).natAbs by simp] at u
              rw [Int.natAbs_dvd_natAbs] at u
              tauto
          rw [show n ^ 2 = n * n by ring]
          apply IsCoprime.mul_right
          exact o2
          exact o2

        rw [show (9: ℤ) = 3 * 3 by norm_num]
        apply IsCoprime.mul_left
        exact o1
        exact o1
      replace d: 9 ∣ n ^ 2 * (n - 1) := by
        rw [← h2]
        simp
      have l:= IsCoprime.dvd_of_dvd_mul_left pp d
      apply exists_eq_mul_right_of_dvd at l
      obtain ⟨m, hm⟩ := l
      have lm: 0 ≤ m := by
        omega
      replace hm: n = 9 * m + 1 := by omega
      simp [hm] at h2
      replace h2: x = m * (9 * m + 1) ^ 2 := by nlinarith
      simp [h2,hm] at h1
      replace h1: y = (9 * m + 1) ^ 2 * (1 - m) := by nlinarith
      have o: 0 ≤ 1 - m := by nlinarith
      replace o: m ≤ 1 := by omega
      interval_cases m <;> simp [hm]

  -- the backward direction
  . intro h
    simp at h
    rcases h with h | h | h | h | h | h
    -- case 1: n = 0
    . simp [h]
      use 0
      norm_num

    -- case 2: n = 1
    . simp [h]
      use 0
      norm_num

    -- case 3: n = 3
    . simp [h]
      use 2
      norm_num
      use 7
      norm_num

    -- case 4: n = 6
    . simp [h]
      use 20
      norm_num
      use 16
      norm_num

    -- case 5: n = 9
    . simp [h]
      use 72
      norm_num
      use 9
      norm_num

    -- case 6: n = 10
    . simp [h]
      use 100
      norm_num
