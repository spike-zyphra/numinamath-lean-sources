import Mathlib

/- Given m and k ≤ n and that m divides n, then m divides n - k iff m divides k. -/
lemma dvd_sub_iff_right {m n k : Nat} (hkn : k ≤ n) (h : m ∣ n) : m ∣ n - k ↔ m ∣ k := by
  refine ⟨?_, Nat.dvd_sub hkn h⟩
  let ⟨x, hx⟩ := h
  cases hx
  intro hy
  let ⟨y, hy⟩ := hy
  have hk : k = m * (x - y) := by
    rw [Nat.sub_eq_iff_eq_add hkn] at hy
    rw [Nat.mul_sub, hy, Nat.add_comm, Nat.add_sub_cancel]
  exact hk ▸ Nat.dvd_mul_right _ _

/- Given m and k ≤ n and that m divides k, then m divides n - k iff m divides n. -/
lemma dvd_sub_iff_left {m n k : Nat} (hkn : k ≤ n) (h : m ∣ k) : m ∣ n - k ↔ m ∣ n := by
  rw (occs := [2]) [← Nat.sub_add_cancel hkn]
  exact Nat.dvd_add_iff_left h

/- 9.15 A circle has 1956 digits. It is known that starting from a certain digit and recording these numbers in a clockwise direction, a 1956-digit number is obtained that is divisible by 27. Prove that if starting from any digit and recording these digits in a clockwise direction, the resulting 1956-digit number is also divisible by 27.
(Kyiv Mathematical Olympiad, 1956) -/
theorem number_theory_137791 (a : Fin 1956 → ℕ) (h : ∀ i, a i < 10)
  (hd : 27 ∣ Nat.ofDigits 10 (List.ofFn a)) (k : ℕ) :
  27 ∣ Nat.ofDigits 10 ((List.ofFn a).rotate k) := by

    -- the theorem is true for 3 * n digits, so we prove the more general theorem, for 1956 = 3 * n
    have as_three : 1956 = 3 * 652 := by omega
    generalize 1956 = x at *
    generalize 652 = n at *
    subst as_three

    -- n = 0 is trivial
    by_cases hn : n = 0
    · norm_num [hn]

    -- we prove by induction on k
    induction' k with k kh
    -- we are given that the base case is true
    · simpa only [List.rotate_zero] using hd

    -- then we just need to prove that given digits A, it's true when we rotate the digits 1 step
    · rw [←List.rotate_rotate]
      generalize hA : ((List.ofFn a).rotate k) = A at *

      -- we have more than 0 digits
      have A_length_pos : 0 < A.length := by
        simpa only [←hA, List.length_rotate, List.length_ofFn,
          Nat.ofNat_pos, mul_pos_iff_of_pos_left] using Nat.zero_lt_of_ne_zero hn

      -- let the first element be a_0
      obtain ⟨a0, rest, rfl⟩ := List.exists_cons_of_length_pos A_length_pos

      -- we want to prove that 27 divides a_1,a_2,..,a_n,a_0
      simp only [List.rotate_cons_succ, List.rotate_zero]

      -- consider the difference 10 * (a_1,a_2,..,a_n,a_0) - a_0,a_1,..,a_n
      -- which equal (10 ^ (3 * n) - 1) * a_0
      have sub_eq : 10 * (Nat.ofDigits 10 (rest ++ [a0])) - (Nat.ofDigits 10 (a0 :: rest))
        = (10 ^ (3 * n) - 1) * a0 := by
          -- split out a_0
          rw [Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_singleton]

          -- simplify
          rw [mul_add, add_comm (10 * _), Nat.add_sub_add_right]
          have ten_pow_eq : 10 * (10 ^ rest.length * a0) = 10 ^ (rest.length + 1) * a0 := by ring
          rw [ten_pow_eq]

          -- the length of A is 3 * n
          have A_length : (a0 :: rest).length = 3 * n := by
            rw [←hA]
            norm_num

          -- simplify
          norm_num [←A_length, Nat.sub_mul]

      -- 27 divides (10 ^ (3 * n) - 1) * a_0
      have dvd_sub : 27 ∣ (10 ^ (3 * n) - 1) * a0 := by
        -- ignore a_0
        refine Dvd.dvd.mul_right ?_ a0

        -- consider 1000 ^ n - 1
        rw [Nat.pow_mul]
        norm_num

        -- 1000 ≡ 1 (mod 27)
        have mod_27 : 1000 % 27 = 1 := by omega

        -- 1000 ^ n ≡ 1 (mod 27)
        have mod_27_pow : 1000 ^ n % 27 = 1 := by
          norm_num [Nat.pow_mod, mod_27]

        -- 1000 ^ n - 1 ≡ 0 (mod 27)
        have mod_sub : (1000 ^ n - 1) % 27 = 0
          := Nat.sub_mod_eq_zero_of_mod_eq mod_27_pow

        -- so 27 divides 1000 ^ n - 1
        exact Nat.dvd_of_mod_eq_zero mod_sub

      -- so we have that 27 divides our difference
      rw [←sub_eq] at dvd_sub

      -- the left part is larger than the right part in the difference
      have lee : Nat.ofDigits 10 (a0 :: rest) ≤ 10 * Nat.ofDigits 10 (rest ++ [a0]) := by
        rw [Nat.ofDigits_cons]
        rw [Nat.ofDigits_append]
        norm_num
        rw [mul_add, add_comm a0]
        gcongr
        rw [←mul_assoc]
        refine Nat.le_mul_of_pos_left a0 ?_
        positivity

      -- given that 27 divides Nat.ofDigits 10 (a0 :: rest)
      -- we have that 27 divides 10 * Nat.ofDigits 10 (rest ++ [a0])
      rw [dvd_sub_iff_left lee kh] at dvd_sub

      -- 27 and 10 is coprime
      have coprime : Nat.Coprime 27 10 := by decide

      -- so 27 divides Nat.ofDigits 10 (rest ++ [a0])
      rw [Nat.Coprime.dvd_mul_left coprime] at dvd_sub

      -- as we wanted
      exact dvd_sub