import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- For even positive integer  $n$  we put all numbers  $1,2,...,n^2$  into the squares of
  an  $n\times n$  chessboard (each number appears once and only once).
  Let  $S_1$  be the sum of the numbers put in the black squares and
  $S_2$  be the sum of the numbers put in the white squares.
  Find all  $n$  such that we can achieve  $\frac{S_1}{S_2}=\frac{39}{64}.$-/
theorem number_theory_8506 (n : ℕ)
: (∃ S1, ∃ S2, S1 + S2 = ∑ i ∈ Finset.range (n^2), (i + 1) ∧ 64 * S1 = 39 * S2) ↔
  ∃ k, n = 103 * k := by
    -- We start by an auxiliary lemma which the sum of the first \( n^2 \) natural numbers is:
    -- \[
    -- \sum_{i=1}^{n^2} i = \frac{n^2(n^2 + 1)}{2}
    -- \]
    have aux : ∀ n, ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by
      intro n
      refine Nat.eq_div_of_mul_eq_right (by simp) ?h
      rw [Finset.sum_add_distrib, mul_add, mul_comm, Finset.sum_range_id_mul_two]
      simp [Nat.mul_sub, mul_add]
      rw [←Nat.sub_add_comm]
      omega
      nlinarith
    -- 2 divides the products of two consecutive natural numbers.
    have aux2 (n : ℕ) : 2 ∣ n * (n + 1) := by
      by_cases h : n % 2 = 0
      · replace h :=  Nat.dvd_of_mod_eq_zero h
        exact Dvd.dvd.mul_right h (n + 1)
      · have : n % 2 < 2 := Nat.mod_lt n (by linarith)
        have h : n % 2 = 1 := by simp at *; linarith
        have : (n + 1) % 2 = 0 := by rw [Nat.add_mod]; simp [h]
        have := Nat.dvd_of_mod_eq_zero this
        exact Dvd.dvd.mul_left this n
    constructor <;> intro h
    · obtain ⟨s1, s2, hsum, hrat⟩ := h
      replace hsum : 2 * (s1 + s2) = n^2 * (n^2 + 1)  := by
        rw [hsum, aux (n^2)]
        exact Nat.mul_div_cancel' (aux2 (n ^ 2))
      -- We are given that:
      -- \[
      -- 64S_1 = 39S_2
      -- \]
      -- So we have
      -- \[
      -- 103 * 2 * s1 = n^2 * (n^2 + 1) * 39
      -- \], implies $ 103 \mid n^2 * (n^2 + 1).
      have h1 : 103 * 2 * s1 = n^2 * (n^2 + 1) * 39:= by
        linarith
      have h2 : 103 ∣ n^2 * (n^2 + 1) := by
        have : 103 ∣ n^2 * (n^2 + 1) * 39 := by
          rw [←h1, mul_assoc]; exact Nat.dvd_mul_right 103 (2 * s1)
        exact (Nat.Coprime.dvd_mul_right (by exact rfl)).1 this
      -- Since \( 103 \) is a prime number, it must divide either \( n^2 \) or \( n^2 + 1 \).
      have h3 : 103 ∣ n ^ 2 ∨ 103 ∣ n ^ 2 + 1 :=
        (Nat.Prime.dvd_mul (by decide)).1 h2
      rcases h3 with h3 | h3
      · -- if \( 103 \) divides \( n^2 \), which implies \( 103 \mid n \).
        exact Nat.Prime.dvd_of_dvd_pow (by decide) h3
      · -- \( 103 \) cannot divide \( n^2 + 1 \).
        have c1 : n^2 + 1 ≡ 0 [MOD 103] := ModEq.symm (Dvd.dvd.zero_modEq_nat h3)
        have : n % 103 < 103 :=  Nat.mod_lt n (by simp)
        have a1 : n % 103 ≡ n [MOD 103] := mod_modEq n 103
        replace c1 := (Nat.ModEq.add (Nat.ModEq.pow 2 a1) Nat.ModEq.rfl).trans c1
        interval_cases n % 103 <;> tauto
    · -- Let \( n = 103k \) for some integer \( k \).
      -- We need to check if such \( n \) satisfies the condition.
      obtain ⟨k, hk⟩ := h
      -- Let \[
      -- S_1 = \frac{39 \cdot 103 k^2 (103^2 k^2 + 1)}{2}
      -- \]
      -- \[
      -- S_2 = \frac{64 \cdot 103 k^2 (103^2 k^2 + 1)}{2}
      -- \]
      use 39 * (103^2 * k^2 * (103^2 * k^2 + 1) / 2) / 103 , 64 * (103^2 * k^2 * (103^2 * k^2 + 1) / 2) / 103
      constructor
      · -- Check that $S1 + S2 = n^2 * (n^2 + 1) / 2$.
        have : 103 ∣ 39 * (103 ^ 2 * k ^ 2 * (103 ^ 2 * k ^ 2 + 1) / 2) := by
          apply dvd_mul_of_dvd_right
          rw [Nat.dvd_div_iff_mul_dvd (aux2 (103^2 * k^2))]
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (aux2 (103^2 * k^2))
            (by rw [mul_assoc]; exact (show 103 ∣ 103^2 from dvd_of_mod_eq_zero rfl).trans (
              Nat.dvd_mul_right (103 ^ 2) (k ^ 2 * (103 ^ 2 * k ^ 2 + 1))) )
        rw [aux (n^2), hk]
        rw [←Nat.add_div_of_dvd_right this, ←add_mul]
        simp [mul_pow]
      · -- Check that \( \frac{S_1}{S_2} = \frac{39}{64} \).
        have : 64 * 39 * (103^2 * k^2 * (103^2 * k^2 + 1) / 2) = 39 * 64 * (103^2 * k^2 * (103^2 * k^2 + 1) / 2) := by
          linarith
        rw [←Nat.mul_div_assoc 64 _]
        nth_rw 2 [←Nat.mul_div_assoc 39 _]
        omega
        · apply dvd_mul_of_dvd_right
          rw [Nat.dvd_div_iff_mul_dvd (aux2 (103^2 * k^2))]
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (aux2 (103^2 * k^2))
            (by rw [mul_assoc]; exact (show 103 ∣ 103^2 from dvd_of_mod_eq_zero rfl).trans (
              Nat.dvd_mul_right (103 ^ 2) (k ^ 2 * (103 ^ 2 * k ^ 2 + 1))) )
        · apply dvd_mul_of_dvd_right
          rw [Nat.dvd_div_iff_mul_dvd (aux2 (103^2 * k^2))]
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) (aux2 (103^2 * k^2))
            (by rw [mul_assoc]; exact (show 103 ∣ 103^2 from dvd_of_mod_eq_zero rfl).trans (
              Nat.dvd_mul_right (103 ^ 2) (k ^ 2 * (103 ^ 2 * k ^ 2 + 1))) )
