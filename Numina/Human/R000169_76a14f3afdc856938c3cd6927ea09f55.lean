import Mathlib

/- # Problem:
 40 Let $n$ be a positive integer greater than 10, and each digit of $n$ is $1$, $3$, $7$, or $9$. Prove: $n$ has a prime factor greater than 10.
We will use proof by contradiction. Assume that every prime factor of \( n \) is not greater than 10. Given the conditions, we know that \( n \) is an odd number and that \( n \) is not a multiple of 5. Therefore, we can express \( n \) in the form: \[ n = 3^{i} \cdot 7^{j} \] for some non-negative integers \( i \) and \( j \).

Next, we will consider the remainders of \( 3^{i} \) and \( 7^{j} \) when divided by 20. For \( i = 0, 1, 2, \ldots \) and \( j = 0, 1, 2, \ldots \), we have the following sequences: \[ \begin{array}{l} \{3^{i} \mod 20\}: 1, 3, 9, 7, 1, 3, \ldots \\ \{7^{j} \mod 20\}: 1, 7, 9, 3, 1, 7, \ldots \end{array} \]

Both sequences are periodic with a period of 4. Therefore, we can write: \[ 3^{i} \cdot 7^{j} \equiv a \cdot b \mod 20 \] where \( a \) and \( b \) are values from the sets \( \{1, 3, 7, 9\} \).

Calculating the possible products, we find: \[ 3^{i} \cdot 7^{j} \equiv 1, 3, 7, \text{ or } 9 \mod 20. \]

This indicates that all numbers of the form \( 3^{i} \cdot 7^{j} \) have an even digit in the tens place. However, since every digit of \( n \) is either 1, 3, 7, or 9, which are all odd digits, this leads to a contradiction.

Thus, we conclude that \( n \) must have a prime factor greater than 10. -/

lemma factorization_subset_primeFactors {n : ℕ} {F : Finset ℕ} (hn : n > 0) (hnF : n.primeFactors ⊆ F) (hF : ∀ p ∈ F, p.Prime): ∏ p ∈ F, p ^ n.factorization p = n := by
  nth_rw 2 [← Nat.factorization_prod_pow_eq_self (show n ≠ 0 by omega)]
  rw [Nat.prod_factorization_eq_prod_primeFactors]
  symm
  apply Finset.prod_subset hnF
  intro p hp1 hp2
  suffices n.factorization p = 0 by rw [this]; norm_num
  apply Nat.factorization_eq_zero_of_not_dvd
  contrapose hp2
  simp at hp2 ⊢
  exact ⟨hF p hp1, hp2, by omega⟩

lemma mod_20_case {i j}: (3 ^ i * 7 ^ j) % 20 ∈ ({1, 3, 7, 9} : Finset ℕ) := by
  have h1 : ∀ i : ℕ, (3 : ℕ) ^ i % 20 = 1 ∨ (3 : ℕ) ^ i % 20 = 3 ∨ (3 : ℕ) ^ i % 20 = 7 ∨ (3 : ℕ) ^ i % 20 = 9 := by
    intro i
    induction i with
    | zero =>
      simp
    | succ i ih =>
      have h2 : (3 : ℕ) ^ (i + 1) % 20 = ((3 : ℕ) ^ i * 3) % 20 := by ring_nf
      rw [h2]
      rcases ih with (h | h | h | h) <;> simp [Nat.mul_mod, h]
  have h2 : ∀ j : ℕ, (7 : ℕ) ^ j % 20 = 1 ∨ (7 : ℕ) ^ j % 20 = 3 ∨ (7 : ℕ) ^ j % 20 = 7 ∨ (7 : ℕ) ^ j % 20 = 9 := by
    intro j
    induction j with
    | zero =>
      simp
    | succ j ih =>
      have h2 : (7 : ℕ) ^ (j + 1) % 20 = ((7 : ℕ) ^ j * 7) % 20 := by ring_nf
      rw [h2]
      rcases ih with (h | h | h | h) <;> simp [Nat.mul_mod, h]
  have h3 : (3 ^ i : ℕ) % 20 = 1 ∨ (3 ^ i : ℕ) % 20 = 3 ∨ (3 ^ i : ℕ) % 20 = 7 ∨ (3 ^ i : ℕ) % 20 = 9 := h1 i
  have h4 : (7 ^ j : ℕ) % 20 = 1 ∨ (7 ^ j : ℕ) % 20 = 3 ∨ (7 ^ j : ℕ) % 20 = 7 ∨ (7 ^ j : ℕ) % 20 = 9 := h2 j
  have h5 : (3 ^ i * 7 ^ j) % 20 = ( (3 ^ i : ℕ) % 20 * (7 ^ j : ℕ) % 20 ) % 20 := by
    simp [Nat.mul_mod]
  rw [h5]
  rcases h3 with (h3 | h3 | h3 | h3) <;> rcases h4 with (h4 | h4 | h4 | h4) <;> simp [Finset.mem_insert, Finset.mem_singleton, Nat.mul_mod, h3, h4]


theorem number_theory_7766 (n : ℕ) (h₀ : n > 10) (h₁ : ∀ d ∈ Nat.digits 10 n, d = 1 ∨ d = 3 ∨ d = 7 ∨ d = 9) :
    ∃ p, Nat.Prime p ∧ p > 10 ∧ p ∣ n := by

  by_contra hp
  simp at hp

  have h1: n.primeFactors ⊆ {3, 7} := by
    intro x hx
    simp at hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    by_cases h : 10 < x
    . have := hp x hx1 h
      contradiction
    . have : n % 10 ∈ Nat.digits 10 n := by
        rw [@Nat.digits_of_two_le_of_pos n 10 (by omega) (by omega)]
        simp

      have := h₁ (n % 10) this

      interval_cases x
      all_goals simp
      all_goals contrapose hx1; try decide
      all_goals omega

  have h2: n % 20 ∈ ({1, 3, 7, 9} : Finset ℕ) := by
    have := @factorization_subset_primeFactors n {3, 7} (by omega) h1 (by intro p hp; simp at hp; rcases hp with rfl | rfl; all_goals norm_num)
    rw [Finset.prod_pair (by norm_num)] at this
    rw [← this]
    apply mod_20_case



  have h3: ((n / 10) % 10) % 2 = 0 := by
    simp at h2
    omega

  have h4: (n / 10) % 10 ∈ Nat.digits 10 n := by
    rw [@Nat.digits_of_two_le_of_pos n 10 (by omega) (by omega)]
    rw [@Nat.digits_of_two_le_of_pos (n/10) 10 (by omega) (by omega)]
    simp

  have := h₁ ((n / 10) % 10) h4
  rcases this with h | h | h | h
  all_goals rw [h] at h3; simp at h3
