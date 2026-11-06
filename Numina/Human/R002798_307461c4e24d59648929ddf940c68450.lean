import Mathlib

-- define a sequence, which will be used later
def b (n: ℕ): ℕ :=
  if n = 0 then 3
  else if n = 1 then 3
  else if n = 2 then 5
  else if n = 3 then 11
  else 0

-- prove a simple bound for prime numbers
lemma le_two_prime_le (n: ℕ) (h: Nat.Prime n): 2 ≤ n := by
  by_contra! l
  interval_cases n
  .
    norm_num at h
  .
    norm_num at h

/- What is the largest number of different natural numbers that can be chosen
so that the sum of any three of them is a prime number?-/

theorem number_theory_115283: IsGreatest {N | ∃ a: ℕ → ℕ, (∀ n, n < N → Nat.Prime (a n)) ∧
  (∀ i j k, i < j ∧ j < k ∧ k < N → Nat.Prime (a i + a j + a k))} 4 := by

  constructor

  -- show that 4 is in the set
  .
    simp
    use b
    constructor
    .
      intro n hn
      interval_cases n
      all_goals simp [b]; norm_num
    .
      intro i j k hi hj hk
      interval_cases k <;> interval_cases j <;> interval_cases i <;> simp [b]
      all_goals norm_num


  -- show that 4 is the largest
  .
    intro N hN
    by_contra! l
    simp only [Set.mem_setOf_eq] at hN
    obtain ⟨a, h1, h2⟩ := hN

    -- it suffices to show that it's impossible for N = 5
    replace h1: ∀ n ≤ 4, Nat.Prime (a n) := by
      intro n hn
      specialize h1 n (by omega)
      exact h1
    replace h2: ∀ i j k, i < j ∧ j < k ∧ k ≤ 4 → Nat.Prime (a i + a j + a k) := by
      intro i j k h
      specialize h2 i j k (by omega)
      exact h2
    clear l


    -- we present the first asertion: there are only two cases for a_n % 3
    have f1: (∀ n, n ≤ 4 → (a n % 3 = a 0 % 3 ∨ a n % 3 = (a 0 + 1) % 3)) ∨
      (∀ n, n ≤ 4 → (a n % 3 = a 0 % 3 ∨ a n % 3 = (a 0 + 2) % 3)) := by
      by_contra! f
      rcases f with ⟨f, g⟩
      obtain ⟨u, u1, u2, u3⟩ := f
      obtain ⟨v, v1, v2, v3⟩ := g

      -- then a_u % 3 = (a_0 + 2) % 3, a_v % 3 = (a_0 + 1) % 3
      have du: a u % 3 = (a 0 + 2) % 3 := by omega
      have dv: a v % 3 = (a 0 + 1) % 3 := by omega
      clear u2 u3 v2 v3
      have d: 3 ∣ a 0 + a u + a v := by
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod]
        rw [show (a 0 + a u) % 3 = (a 0 % 3 + a u % 3) % 3 by rw [Nat.add_mod]]
        rw [du]
        rw [dv]
        simp
        omega
      have pi:= h1 u (by omega)
      have pj:= h1 v (by omega)
      have si:= le_two_prime_le (a u) pi
      have sj:= le_two_prime_le (a v) pj
      rw [Nat.prime_dvd_prime_iff_eq] at d
      specialize h1 0 (by omega)
      have s0:= le_two_prime_le (a 0) h1
      omega
      norm_num

      -- we show that 0, u, v are distinct
      have iu: 0 < u := by
        by_contra! o
        replace o: u = 0 := by
          omega
        simp [o] at du
        omega
      have iv: 0 < v := by
        by_contra! o
        replace o: v = 0 := by
          omega
        simp [o] at dv
        omega
      have t: u ≠ v := by
        by_contra! o
        simp [o] at du
        simp [du] at dv
        omega

      by_cases l: u < v
      .
        specialize h2 0 u v (by omega)
        exact h2
      .
        specialize h2 0 v u (by omega)
        rw [show a 0 + a u + a v = a 0 + a v + a u by ring]
        exact h2


    --then there must be 3 numbers mod 3 the same, this is just due to pigeonhole principle, but tricky to formalize
    have f2: ∃ i j k, i < j ∧ j < k ∧ k ≤ 4 ∧ a i % 3 = a j % 3 ∧ a j % 3 = a k % 3 := by
      rcases f1 with f | f
      -- case 1
      .
        have g1:= f 1 (by omega)
        have g2:= f 2 (by omega)
        have g3:= f 3 (by omega)
        have g4:= f 4 (by omega)
        rcases g1 with g1 | g1
        .
          rcases g2 with g2 | g2
          .
            use 0, 1, 2
            simp [g1, g2]
          .
            rcases g3 with g3 | g3
            .
              use 0, 1, 3
              simp [g1, g3]
            .
              rcases g4 with g4 | g4
              .
                use 0, 1, 4
                simp [g1, g4]
              .
                use 2, 3, 4
                simp [g2, g3, g4]
        .
          rcases g2 with g2 | g2
          .
            rcases g3 with g3 | g3
            .
              use 0, 2, 3
              simp [g2, g3]
            .
              rcases g4 with g4 | g4
              .
                use 0, 2, 4
                simp [g2, g4]
              .
                use 1, 3, 4
                simp [g3, g4, g1]
          .
            rcases g3 with g3 | g3
            .
              rcases g4 with g4 | g4
              .
                use 0, 3, 4
                simp [g3, g4]
              .
                use 1, 2, 4
                simp [g1, g2, g4]
            .
              use 1, 2, 3
              simp [g1, g2, g3]

      -- case 2
      .
        have g1:= f 1 (by omega)
        have g2:= f 2 (by omega)
        have g3:= f 3 (by omega)
        have g4:= f 4 (by omega)
        rcases g1 with g1 | g1
        .
          rcases g2 with g2 | g2
          .
            use 0, 1, 2
            simp [g1, g2]
          .
            rcases g3 with g3 | g3
            .
              use 0, 1, 3
              simp [g1, g3]
            .
              rcases g4 with g4 | g4
              .
                use 0, 1, 4
                simp [g1, g4]
              .
                use 2, 3, 4
                simp [g2, g3, g4]
        .
          rcases g2 with g2 | g2
          .
            rcases g3 with g3 | g3
            .
              use 0, 2, 3
              simp [g2, g3]
            .
              rcases g4 with g4 | g4
              .
                use 0, 2, 4
                simp [g2, g4]
              .
                use 1, 3, 4
                simp [g3, g4, g1]
          .
            rcases g3 with g3 | g3
            .
              rcases g4 with g4 | g4
              .
                use 0, 3, 4
                simp [g3, g4]
              .
                use 1, 2, 4
                simp [g1, g2, g4]
            .
              use 1, 2, 3
              simp [g1, g2, g3]


    -- then we use i j k to derive contradiction
    clear f1
    obtain ⟨i, j, k, l1, l2, l3, d1, d2⟩ := f2
    specialize h2 i j k (by omega)
    have d: 3 ∣ a i + a j + a k := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod]
      rw [show (a i + a j) % 3 = (a i % 3 + a j % 3) % 3 by rw [Nat.add_mod]]
      rw [d1]
      rw [d2]
      simp
      omega
    have pi:= h1 i (by omega)
    have pj:= h1 j (by omega)
    have pk:= h1 k (by omega)
    have si:= le_two_prime_le (a i) pi
    have sj:= le_two_prime_le (a j) pj
    have sk:= le_two_prime_le (a k) pk
    rw [Nat.prime_dvd_prime_iff_eq] at d
    omega
    norm_num
    exact h2