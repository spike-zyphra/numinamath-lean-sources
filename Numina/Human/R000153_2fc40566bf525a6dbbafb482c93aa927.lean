import Mathlib


/-- Show that if $\( r \)$ and $\( n \)$ are relatively prime positive integers with $\( n > 0 \)$, and if $\( r \)$ is a primitive root modulo $\( n \)$, then the integers 
$$ r^{1}, r^{2}, \ldots, r^{\phi(n)} $$
form a reduced residue system modulo $\( n \)$.-/
theorem number_theory_4987 (r n : Nat) (h : r.Coprime n) (hr : 0 < r)
  (hn : 0 < n) (h1 : orderOf (r : ZMod n) = n.totient) :
  -- just need to prove each of these powers is relatively prime to $n$ and
  -- no two of these powers are congruent modulo $n$.
  ∀ i ∈ Finset.Icc 1 n.totient, ∀ j ∈ Finset.Icc 1 n.totient,
    (r ^ i).Coprime n ∧ (r ^ i ≡ r ^ j [MOD n] → i = j) := by
    intro i hi j hj
    constructor
    · exact Nat.Coprime.pow_left i h
    · intro h2
      -- with loss of generality, assume $i < j$
      wlog h3 : i < j
      · push_neg at h3
        by_cases h4 : i = j
        · exact h4
        · replace h3 : j < i := by omega
          exact (this r n h hr hn h1 j hj i hi h2.symm h3).symm
      · replace h2 : r ^ (j - i) ≡ 1 [MOD n] := by
          have h4 := Nat.ModEq.dvd h2
          replace h4 : (n :) ∣ r ^ i * (r ^ (j - i) - 1) := by
            simp [Nat.mul_sub, ←pow_add, show i + (j - i) = j by refine Nat.add_sub_of_le (le_of_lt h3)]
            rw [←Nat.cast_sub (Nat.pow_le_pow_of_le_right hr (le_of_lt h3))] at h4
            zify; exact h4
          apply Nat.modEq_of_dvd
          replace h4 : n ∣ (r ^ (j - i) - 1) :=
            (Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_left i h).symm).1 h4
          zify at h4
          rw [←Int.dvd_neg, Nat.cast_sub (Nat.one_le_pow (j - i) r hr), Int.neg_sub] at h4
          exact h4
        have h4 : (r : ZMod n) ^ (j - i) = (1 : ℕ) := by
          rw [←Nat.cast_pow, ZMod.eq_iff_modEq_nat]
          exact h2
        simp at h4
        -- This implies that $i−j$ must be a multiple of $\phi(n)$
        have h5 := orderOf_dvd_iff_pow_eq_one.2 h4
        simp [h1] at h5
        -- Because $j - i <$ `n.totient` and `n.totient ∣ j-i`, we get $j-i$ equal zero, i.e. $i = j$.
        have h6 : j - i < n.totient := by
          calc
            _ ≤ n.totient - 1 := by exact tsub_le_tsub (Finset.mem_Icc.1 hj).2 (Finset.mem_Icc.1 hi).1
            _ < n.totient := Nat.sub_one_lt (Nat.ne_zero_iff_zero_lt.mpr (
              Nat.totient_pos.mpr hn))
        have := Nat.le_of_sub_eq_zero <| Nat.eq_zero_of_dvd_of_lt h5 h6
        exfalso; exact Nat.not_lt_of_le this h3
