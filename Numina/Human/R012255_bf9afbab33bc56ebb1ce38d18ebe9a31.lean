import Mathlib

/- ## Task B-1.5.


Prove that for every $n \in \mathbb{N}$, exactly one of the numbers $A_{n}=2^{2 n+1}-2^{n+1}+1$ and $B_{n}=2^{2 n+1}+2^{n+1}+1$ is divisible by 5. -/

-- Five divides product of our two numbers.
lemma five_div_mul (n:ℕ): (5 ∣ (2^(2*n + 1) - 2^(n + 1) + 1) * (2^(2*n + 1) + 2^(n + 1) + 1)) := by {
  rw[<-Nat.sub_add_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_comm (2^(n+1)), <-Nat.add_assoc]
  rw[←Nat.sq_sub_sq, <-pow_mul, add_sq, mul_one, <-pow_mul, pow_two, mul_one, <-pow_succ']
  rw[add_assoc (2*n), add_assoc, add_comm (2 ^ (2 * n + (1+1))), ←add_assoc, add_mul (n),
mul_comm n]
  simp only [Nat.reduceAdd, add_tsub_cancel_right]
  rw[add_mul, mul_comm (2*n), ←mul_assoc, pow_add, pow_mul]
  simp only [Nat.reduceMul, Nat.reducePow, one_mul]
  rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]
  simp only [Nat.reduceMod, one_pow, Nat.one_mod, Nat.mod_succ, one_mul, Nat.reduceAdd,
Nat.mod_self]

  apply Nat.pow_le_pow_of_le; simp only [Nat.one_lt_ofNat];
  apply Nat.add_le_add_right
  apply Nat.le_mul_of_pos_left
  simp only [Nat.ofNat_pos]
}

-- But five does not divide the sum of our two numbers.
lemma five_not_div_mul (n:ℕ): ¬(5 ∣ (2^(2*n + 1) - 2^(n + 1) + 1) + (2^(2*n + 1) + 2^(n + 1) + 1)) := by {
  have h1 : (2 ^ (2 * n + 1) - 2 ^ (n + 1) + 1) + (2 ^ (2 * n + 1) + 2 ^ (n + 1) + 1) = 2 ^ (2 * n + 2) + 2 := by {
    ring_nf
    rw[Nat.add_assoc 2,Nat.add_assoc 2, Nat.add_left_cancel_iff, Nat.sub_add_cancel, <-Nat.mul_add]
    simp only [Nat.reduceAdd]
    rw[mul_le_mul_right]
    apply Nat.pow_le_pow_right; simp;
    apply  Nat.le_mul_of_pos_right n ?_
    simp; simp;
  }

  rw[h1, pow_add, pow_mul]
  simp only [Nat.reducePow]
  rw[Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod]
  by_cases h: Even n; {

    cases h with |intro k h =>
    rw[h, pow_add, <-mul_pow, Nat.pow_mod]
    simp only [Nat.reduceMul, Nat.reduceMod, one_pow, Nat.one_mod, Nat.mod_succ, one_mul,
      Nat.reduceAdd, one_ne_zero, not_false_eq_true]
  }; {
    rw[Nat.not_even_iff_odd, Odd] at h
    cases h with |intro k h =>
    rw[h, pow_add, pow_mul, Nat.mul_mod ((4 ^ 2) ^ k), Nat.pow_mod]
    simp only [Nat.reducePow, Nat.reduceMod, one_pow, Nat.one_mod, pow_one, Nat.mod_succ, one_mul,
      Nat.reduceMul, Nat.reduceAdd, OfNat.ofNat_ne_zero, not_false_eq_true]
  }
}

--So, exactly one of the numbers can be divisible by five.
theorem number_theory_211466 (n : ℕ) :
    (5 ∣ 2^(2*n + 1) - 2^(n + 1) + 1 ∧ ¬5 ∣ 2^(2*n + 1) + 2^(n + 1) + 1) ∨
    (¬5 ∣ 2^(2*n + 1) - 2^(n + 1) + 1 ∧ 5 ∣ 2^(2*n + 1) + 2^(n + 1) + 1) := by {
  rw[and_or_right, or_and_left, or_and_left]
  simp[em, em']
  apply And.intro; {
    rw[←Nat.Prime.dvd_mul]
    apply five_div_mul
    norm_num
  }; {
    rw[<-not_and_or]
    intro h
    cases h with |intro h1 h2 =>
    apply five_not_div_mul
    apply Nat.dvd_add h2 h1
  }
}