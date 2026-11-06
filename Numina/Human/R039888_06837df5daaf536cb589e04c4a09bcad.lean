import Mathlib

/- Zij $\lfloor x\rfloor$ het grootste gehele getal kleiner dan of gelijk aan $x$. Laat $n \in \mathbb{N}, n \geq 7$ gegeven zijn.
Bewijs dat $\binom{n}{7}-\left\lfloor\frac{n}{7}\right\rfloor$ deelbaar is door 7 . -/
theorem number_theory_606121 (n : ℕ) (hn : n ≥ 7) :
  7 ∣ Nat.choose n 7 - n / 7 := by

  -- first we cast the numbers to ℤ to handle subtraction easier
  suffices h : (7 : ℤ) ∣ Nat.choose n 7 - n / 7 by
    have : ↑(Nat.choose n 7 - n / 7) = (Nat.choose n 7 - ↑(n / 7) : ℤ) := by
      refine Int.ofNat_sub ?_
      refine Nat.div_le_of_le_mul ?_
      rw [mul_comm, Nat.choose_succ_right_eq]
      have : n ≤ n.choose 6 := by
        rw [Nat.choose_eq_descFactorial_div_factorial]
        match n with
        |0|1|2|3|4|5|6 => norm_num at hn
        | n + 7 =>
          rw [Nat.succ_descFactorial_succ]
          rw [show n + 6 + 1 = n + 7 by norm_num]
          trans (n + 7) * ((n + 6).descFactorial 5 / Nat.factorial 6)
          swap
          · apply Nat.mul_div_le_mul_div_assoc
          refine Nat.le_mul_of_pos_right (n + 7) ?_
          refine Nat.div_pos_iff.mpr ?_
          constructor
          · exact Nat.factorial_pos 6
          simp
          rw [show Nat.factorial 6 = 2 * (3 * (4 * (5 * 6))) by simp [Nat.factorial]]
          gcongr
          all_goals apply Nat.le_add_left
      nth_rw 1 [show n = n * 1 by ring]
      gcongr
      exact Nat.le_sub_of_add_le hn
    norm_cast at this h
    rw [← this] at h
    norm_cast at h

  -- Write n - 7k + l for integers k and l with 0 ≤ l ≤ 6
  let l := n % 7
  have hn_mod_7_l : n ≡ l [ZMOD 7] := by
    unfold l
    simp
    exact Int.ModEq.symm (Int.mod_modEq (↑n) 7)
  have ⟨k, hk⟩ := Int.modEq_iff_add_fac.mp hn_mod_7_l.symm

  -- then it holds that ⌊n / 7⌋ = k
  have h_n_div_7_k : n / 7 = k := by
    have : (n : ℤ) = (n / 7) * 7 + l := by
      unfold l
      norm_cast
      exact Eq.symm (Nat.div_add_mod' n 7)
    have : k * 7 = (n / 7) * 7 := by linarith
    symm
    apply Int.eq_of_mul_eq_mul_right at this
    exact this
    norm_num

  -- so it suffices to prove that n.choose 7 ≡ k (mod 7)
  suffices h : n.choose 7 ≡ k [ZMOD 7] by
    rw [h_n_div_7_k]
    exact Int.ModEq.dvd (id (Int.ModEq.symm h))

  have : Fact (Nat.Prime 7) := by norm_num; trivial

  -- as 7 is a prime, we have the following fact :
  --  n.choose k ≡ (n % p).choose (k % p)) * (n / p).choose (k / p) (mod p)
  -- with p = k = 7, this simplifies to n.choose 7 ≡ (n / 7).choose 1 = n / 7
  have := Choose.choose_modEq_choose_mod_mul_choose_div (n := n) (k := 7) (p := 7)
  simp at this

  -- so we are done by transitivity
  trans n / 7
  · exact this
  · rw [h_n_div_7_k]
