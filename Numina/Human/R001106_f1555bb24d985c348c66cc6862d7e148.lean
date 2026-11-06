import Mathlib

/-How many different primes appear in the prime factorization of $20!$ (20 factorial)? (Reminder: The number $n!$ is the product of the integers from 1 to $n$.  For example, $5!=5\cdot 4\cdot3\cdot2\cdot 1= 120$.)-/
theorem algebra_20515 : {p : ℕ | p.Prime ∧ p ∣ Nat.factorial 20}.encard = 8 := by
  -- show that the desired set is Nat.primesBelow 20
  have set_eq : {p : ℕ | p.Prime ∧ p ∣ Nat.factorial 20} = Nat.primesBelow 20 := by
    ext n
    simp [Nat.primesBelow]
    apply Iff.intro <;> intro h
    -- show n < 20
    . obtain ⟨h1, h2⟩ := h
      rw [Nat.Prime.dvd_factorial h1] at h2
      -- show that n ≠ 20
      have h3 : n ≠ 20 := by
        intro h
        rw [h] at h1
        norm_num at h1
      -- show that n < 20
      replace h2 : n < 20 := by
        contrapose! h3
        apply Nat.le_antisymm
        all_goals tauto
      tauto
    -- show n ∣ 20!
    . -- show that n ∣ Nat.factorial 20
      have dvd₁ : n ∣ Nat.factorial 20 := by
        cases n with
        | zero => -- when n = 0
          norm_num at h
        | succ n => -- when n = n + 1
          apply Nat.dvd_factorial
          linarith only [h]
          linarith only [h]
      tauto
  -- calculate the encard of Nat.primesBelow 20
  rw [set_eq]
  rw [Set.encard_coe_eq_coe_finsetCard]
  rw [Nat.primesBelow_card_eq_primeCounting']
  norm_cast
