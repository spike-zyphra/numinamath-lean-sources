import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
lemma Nat.add_sub_assoc_of_le {a b c : ℕ } (h : a ≤ a + b - c) : a + b - c = a + (b - c) := by
  have : a + b - b ≤ a + b - c := by simpa
  by_cases hc : c ≤ a + b
  · have := (Nat.sub_le_sub_iff_left hc).1 this
    exact Nat.add_sub_assoc this a
  · push_neg at hc
    have : a = 0 := by rw [Nat.sub_eq_zero_of_le (le_of_lt hc)] at h; linarith
    simp [this]

/- Let $a, b$ be positive integers such that $b^n +n$ is a multiple of $a^n + n$ for all positive integers $n$ . Prove that $a = b.$-/
theorem number_theory_8779 (a b : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : ∀ n : ℕ, 0 < n → ((a ^ n + n) ∣ (b ^ n + n))) :a = b := by
  by_cases h : b ≥ a
  · by_cases h' : b = a
    · --When $a \le b$, if $a = b$, the conclusion is right.
      omega
    · push_neg at h'
      by_contra t
      push_neg at t
      have h1 : b > a := by
        exact Nat.lt_of_le_of_ne h (id (Ne.symm h'))
      have h2 : ∃ p : ℕ , p > b ∧ p.Prime := by
        exact exists_infinite_primes b.succ
      --If $a < b$, we can find a prime $p$ and $p > b$.
      rcases h2 with ⟨p,⟨ha,hb⟩⟩
      have h3 : ∃ n : ℕ , n = (p - 1) * (a + 1) + 1 := by
        exact exists_apply_eq_apply (fun a => a) ((p - 1) * (a + 1) + 1)
      --Let $n = (p - 1)(a + 1) + 1$, the following conclusion is hold.
      rcases h3 with ⟨n,hn⟩
      have h4 : n > 0 := by
        exact Nat.lt_of_sub_eq_succ hn
      have h6 : p ∣ a ^ n - a := by
      --Firstly, we can know that $p \ | \ a ^ n - a$.
        rw[hn]
        have g1 : a ^ ((p - 1) * (a + 1) + 1) - a = (a ^ (p - 1)) ^ (a + 1) * a - a := by
          refine (Nat.sub_eq_iff_eq_add ?h).mpr ?_
          · refine Nat.le_self_pow ?h.hn a
            exact Ne.symm (zero_ne_add_one ((p - 1) * (a + 1)))
          · symm
            rw[add_comm,← add_sub_assoc_of_le,add_comm]
            simp
            symm
            rw[pow_add,pow_mul]
            simp
            refine le_sub_of_add_le ?h
            simp
            refine Nat.le_mul_of_pos_left a ?h.h
            refine pos_pow_of_pos (a + 1) ?h.h.h
            exact pos_pow_of_pos (p - 1) h₀
        have g2 : a ^ (p - 1) ≡ 1 [MOD p] := by
        --By Fermat's little theorem, We have $a ^ {p - 1} \equiv 1 \ (mod \ p)$, becasue $p > b > a$ and $p$ is a prime.
          have w1 : a.Coprime p := by
            have t1 : p.Coprime a := by
              apply Nat.coprime_of_lt_prime
              exact h₀
              linarith
              exact hb
            exact coprime_comm.mp t1
          have w2 : a ^ φ p ≡ 1 [MOD p] := by
            exact Nat.ModEq.pow_totient w1
          have w3 : φ p = p - 1 := by
            exact Nat.totient_prime hb
          rw[← w3]
          exact w2
        refine dvd_of_mod_eq_zero ?H
        rw[g1]
        refine sub_mod_eq_zero_of_mod_eq ?H.h
        rw[mul_mod,pow_mod]
        rw[g2]
        simp
        have g3 : 1 % p = 1 := by
          have w1 : p > 1 := by
            exact Prime.one_lt hb
          exact mod_eq_of_lt w1
        rw[g3]
        simp
      --So
      --$$a ^ n = a \cdot (a ^ {p - 1}) ^ {a + 1} \equiv a \ (mod \ p).$$
      have h7 : p ∣ b ^ n - b := by
      --By the same reason, we can prove $p \ | \ b ^ n - b$.
        rw[hn]
        have g1 : b ^ ((p - 1) * (a + 1) + 1) - b = (b ^ (p - 1)) ^ (a + 1) * b - b := by
          have w1 : b ≤ b ^ ((p - 1) * (a + 1) + 1) := by
            refine Nat.le_self_pow ?hn b
            exact Ne.symm (zero_ne_add_one ((p - 1) * (a + 1)))
          have w2 : b ^ ((p - 1) * (a + 1) + 1) = (b ^ (p - 1)) ^ (a + 1) * b - b + b := by
            symm
            rw[add_comm,← add_sub_assoc_of_le,add_comm]
            simp
            symm
            rw[pow_add,pow_mul]
            simp
            refine le_sub_of_add_le ?h
            simp
            have t1 : 0 < (b ^ (p - 1)) ^ (a + 1) := by
              apply pos_pow_of_pos
              exact pos_pow_of_pos (p - 1) h₁
            apply Nat.le_mul_of_pos_left
            exact t1
          exact (Nat.sub_eq_iff_eq_add w1).mpr w2
        have g2 : b ^ (p - 1) ≡ 1 [MOD p] := by
          have w1 : b.Coprime p := by
            have t1 : p.Coprime b := by
              apply Nat.coprime_of_lt_prime
              exact h₁
              exact ha
              exact hb
            exact coprime_comm.mp t1
          have w2 : b ^ φ p ≡ 1 [MOD p] := by
            exact Nat.ModEq.pow_totient w1
          have w3 : φ p = p - 1 := by
            exact Nat.totient_prime hb
          rw[← w3]
          exact w2
        rw[g1]
        apply dvd_of_mod_eq_zero
        apply sub_mod_eq_zero_of_mod_eq
        rw[mul_mod,pow_mod]
        rw[g2]
        simp
        have g3 : 1 % p = 1 := by
          have w1 : p > 1 := by
            exact Prime.one_lt hb
          exact mod_eq_of_lt w1
        rw[g3]
        simp
      have h8 : p ∣ a + n := by
      --Then it's not hard to prove that $p \ | \ a + n$.
        rw[hn]
        ring_nf
        have g1 : 1 + a + a * (p - 1) + (p - 1) = a * p + p := by
          calc
          _ = a * (p - 1) + a + 1 + (p - 1) := by ring
          _ = a * p - a + a + 1 + (p - 1) := by rw[mul_tsub,mul_one]
          _ = _ := by
            rw[← add_sub_assoc_of_le]
            simp
            rw[add_comm,← add_sub_assoc_of_le]
            simp
            refine le_sub_of_add_le ?h
            refine Nat.add_le_add ?h.h₁ ?h.h₂
            exact Nat.le_refl a
            refine Nat.le_mul_of_pos_right a ?h.h₂.h
            exact zero_lt_of_lt ha
            refine le_sub_one_of_lt ?_
            linarith
          --Because
          --$$a + n \equiv a + (p - 1)(a + 1) + 1 \equiv a + (-1)(a + 1) + 1 \equiv 0 \ (mod \ p)$$
        rw[g1]
        have g2 : p ∣ p := by
          exact dvd_refl p
        have g3 : p ∣ a * p := by
          exact Nat.dvd_mul_left p a
        exact (Nat.dvd_add_iff_right g3).mp g2
      have h9 : p ∣ a ^ n + n  := by
      --Then we can prove $p \ | \ a ^ n + n$ by using  $p \ | \ a + n$ and $p \ | \ a ^ n - a$.
        have g1 : a ^ n + n = a ^ n - a + (a + n) := by
          rw[← add_assoc]
          simp
          symm
          rw[add_comm,← add_sub_assoc_of_le]
          · rw[add_comm]
            simp
          · apply le_sub_of_add_le
            simp
            apply Nat.le_self_pow
            exact not_eq_zero_of_lt h4
        rw[g1]
        exact (Nat.dvd_add_iff_right h6).mp h8
      have h10 : p ∣ b ^ n + n  := by
        exact Nat.dvd_trans h9 (h₂ n h4)
      --According to the conditions,
      --$$p \ | \ a ^ n + n \ | \ b ^ n + n.$$
      have h11 : b - a ≡ b ^ n + n [MOD p] := by
      --And $b - a \equiv b ^ n + n \ (mod \ p)$ because $p \ | \ b ^ n - b$ and $p \ | \ a + n$.
        have g2 : b - a ≤ b ^ n + n := by
          have w1 : b ^ n ≥ b := by
            refine Nat.le_self_pow ?hn b
            exact not_eq_zero_of_lt h4
          have w2 : b > b - a := by
            exact sub_lt h₁ h₀
          linarith
        have g3 : b ^ n + n - (b - a) = (b ^ n - b) + (a + n) := by
          ring_nf
          rw[add_comm]
          have w1 : b ^ n - (b - a) =  (b ^ n - b) + a := by
            calc
            _ = b ^ n - b + a := by
              refine tsub_tsub_assoc ?h₁ h
              refine Nat.le_self_pow ?h₁.hn b
              exact not_eq_zero_of_lt h4
            _ = _ := by exact rfl
          rw[add_assoc,← w1]
          apply Nat.add_sub_assoc
          have w2 : b ^ n ≥ b := by
            refine Nat.le_self_pow ?hn b
          have w4 : b > b - a := by
            exact sub_lt h₁ h₀
          linarith
        refine (modEq_iff_dvd' g2).mpr ?_
        rw[g3]
        exact (Nat.dvd_add_iff_right h7).mp h8
      have h12 : p ∣  b - a := by
      --So, $b - a \equiv b ^ n + n \equiv 0 \ (mod \ p)$.That means $p \ | \ b - a$.
        have g1 : (b - a) % p = 0 := by
          rw[h11]
          exact (dvd_iff_mod_eq_zero).mp h10
        exact dvd_of_mod_eq_zero g1
      have h13 : p ≤ b - a := by
        have g1 : b - a > 0 := by
          exact zero_lt_sub_of_lt h1
        exact le_of_dvd g1 h12
      have h14 : b < b - a := by
        exact Nat.lt_of_lt_of_le ha h13
      have h15 : a < 0 := by
        exact lt_of_tsub_lt_tsub_left h14
      exact not_succ_le_zero a h15
      --But $0 < b - a < p$, that leads to a contradiction.
  · push_neg at h
    --If $a > b$, let $n = 1$, then $a + 1 \ | \ b + 1$,
    have h1 : a ^ 1 + 1 ∣ b ^ 1 + 1 := by
      exact h₂ 1 (by norm_num)
    simp at h1
    have h2 : a + 1 ≤ b + 1 := by
    -- so $a \le b$, that leads to a contradiction.
      apply le_of_dvd
      have g1 : 0 < b + 1 := by linarith
      exact g1
      exact h1
    linarith
    --Sum up, $a = b$.
    --Q.E.D.
