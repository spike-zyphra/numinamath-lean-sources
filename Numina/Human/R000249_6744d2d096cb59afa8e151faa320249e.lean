import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
set_option maxHeartbeats 800000

/- Find all 4-digit numbers  $n$ , such that  $n=pqr$ , where $p < q < r$ are distinct primes,
such that  $p+q=r−qp+q=r-q$  and  $p+q+r=s2p+q+r=s^2$ , where  ss  is a prime number. -/
theorem number_theory_8698 :
  {n : ℕ | ∃ p q r s : ℕ, n = p * q * r ∧ p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r
    ∧ p + q = r - q ∧ p + q + r = s^2 ∧ s.Prime ∧ 1000 ≤ n ∧ n ≤ 9999} = {2015} := by
    ext n; simp
    constructor <;> intro h
    · obtain ⟨p, q, r, h1, hp, hq, hr, pltq, qltr, h2, ⟨s, h3, hs, hn⟩ ⟩ := h
      -- \[
      -- p + q = r - q \implies r = p + 2q
      -- \]
      have h4 : r = p + 2 * q := by
        have := Nat.eq_add_of_sub_eq (le_of_lt qltr) h2.symm
        linarith
      --  \[
      -- p + q + (p + 2q) = s^2 \implies 2p + 3q = s^2
      -- \]
      replace h3 : 2 *p + 3 * q = s ^ 2 := by
        rw [h4] at h3; linarith
      -- \( p \equiv 2 \pmod{3} \)
      have h5 : p ≡ 2 [MOD 3] := by
        have : s ^ 2 ≡ 1 [MOD 3] := by
          have : s % 3 < 3 := mod_lt s (by simp)
          have : s ≡ s % 3 [MOD 3] := ModEq.symm (mod_modEq s 3)
          interval_cases (s % 3)
          · have sne3 : s ≠ 3 := by
              intro tmp; simp [tmp] at h3
              have : q ≤ 3 := by linarith
              interval_cases q
              . exact Nat.not_lt_zero p pltq
              . omega
              · omega
              · simp at h3; simp [h3] at hp; exact Nat.not_prime_zero hp
            have : 3 ∣ s := dvd_of_mod_eq_zero this
            exfalso; exact sne3 ((or_iff_right (by simp)).1 <| (Nat.dvd_prime hs).1 this).symm
          · exact Nat.ModEq.pow 2 this
          · exact Nat.ModEq.pow 2 this
        have h5 : 2 * p + 3 * q ≡ 1 [MOD 3] := (show 2 * p + 3 * q ≡ s ^ 2 [MOD 3] by simp [h3]; rfl).trans this
        rw [←add_zero 1] at h5
        have h6 : 2 * p ≡ 1 [MOD 3] := Nat.ModEq.add_right_cancel (modEq_zero_iff_dvd.mpr (by simp)) h5
        replace h6 : 2 * p ≡ 4 [MOD 3] := h6
        rw [show 4 = 2 * 2 by linarith] at h6
        exact Nat.ModEq.cancel_left_of_coprime (by decide) h6
      rw [h1, h4] at hn
      by_cases p2 : p = 2
      · -- $p = 2$ is impossible.
        rw [p2] at hn
        have := hn.2
        have qlt50 : q < 50 := by
          by_contra! hf
          have : 10000 < 2 * q * (2 + 2 * q) := by
            calc
              _ < 2 * 50 * (2 + 2 * 50) := by decide
              _ ≤ _ := by
                have : ∀ m n, m ≤ n → (2 * m * (2 + 2 * m)) ≤ (2 * n * (2 + 2 * n)) := by
                  intro m n hmn
                  ring_nf
                  exact Nat.add_le_add (by linarith) (by simp; exact Nat.pow_le_pow_of_le_left hmn 2)
                exact this 50 q hf
          linarith
        simp [p2] at h3
        have h6 : s ^ 2 < 154 := h3 ▸ (by linarith)
        replace h6 : s < 13 := by
          have : s ^ 2 < 13 ^ 2 := by linarith
          exact lt_of_pow_lt_pow_left' 2 this
        interval_cases q <;> simp at h3 <;> simp at * <;> (interval_cases s <;> tauto)
      · -- because $p q$ are prime numbers, $p < q$ and $p \ne 2 $, we have $p + 2 \leq q$.
        have h6 : p + 2 ≤ q := by
          have oddp : Odd p := Prime.odd_of_ne_two hp p2
          replace pltq : p + 1 ≤ q := pltq
          have : p + 1 ≠ q := by
            have : Even (p + 1) := even_add'.mpr (by tauto)
            have qne2 : q ≠ 2 := fun tmp => (by simp [tmp] at pltq; linarith [Nat.Prime.two_le hp])
            exact fun tmp => (by
              simp [tmp] at this;
              have oddq := Prime.odd_of_ne_two hq qne2
              exact Nat.not_odd_iff_even.2 this oddq)
          have : p + 1 < q := Nat.lt_of_le_of_ne pltq this
          linarith
        -- To find an upper bound for \( p \), consider the smallest possible values for \( q \) and \( r \):
        -- \[
        -- p \cdot (p+2) \cdot (3p+4) \leq 9999
        -- \]
        -- Testing small primes, we find: \( p \leq 17 \).
        have h7 : p * (p + 2) * (3 * p + 4) ≤ 9999 := by
          calc
            _ = p * (p + 2) * (p + 2 * (p + 2)) := by ring
            _ ≤ p * q * (p + 2 * q) := by
              rw [mul_assoc, mul_assoc];
              refine Nat.mul_le_mul (by linarith) (Nat.mul_le_mul h6 (by linarith))
            _ ≤ 9999 := hn.2
        replace h7 : p < 17 := by
          by_contra! hpp
          have : 17 * (17 + 2) * (3 * 17 + 4) ≤ p * (p + 2) * (3 * p + 4) :=
            Nat.mul_le_mul (Nat.mul_le_mul hpp (by linarith)) (by linarith)
          simp at this
          linarith
        -- Because \( p \equiv 2 \pmod{3} \), $p \ne 2$ and $p < 17$, we have $p$ can only be 5 or 11.
        have h8 : p = 5 ∨ p = 11 := by
          interval_cases p <;> tauto
        have aux : ∀ p q z, 0 < p → q ≤ z → p * q * (p + 2 * q) ≤ p * z * (p + 2 * z) := by
          intro p q z hp hq
          exact Nat.mul_le_mul (Nat.mul_le_mul (by simp) hq) (by linarith)
        rcases h8 with p5 | p11
        · -- Case \( p = 5 \):
        -- \[
        -- 9999 \geq 5 \cdot q \cdot (2q + 5) \implies q \leq 31
        -- \]
          have q13 : q = 13 := by
            have : q ≤ 31 := by
              have := hn.2
              simp [p5] at this
              by_contra! tmp
              have := aux 5 31 q (by simp) (le_of_lt tmp)
              simp at this
              linarith
            have hs : s ^ 2 ≤ 103 := by simp [p5] at h3; exact h3 ▸ (by linarith)
            replace hs : s < 11 := by
              have : s ^ 2 < 121 := by linarith
              exact lt_of_pow_lt_pow_left' 2 this
            interval_cases q <;> simp [p5] at h3 h4 <;> simp at * <;> (interval_cases s <;> try tauto)
            simp [h4] at hr; tauto
          simp [p5, q13] at h4
          simp [p5, q13, h4] at h1
          exact h1
        · -- Case \( p = 11 \):
        -- \[
        -- 9999 \geq 11 \cdot q \cdot (2q + 11) \implies q \leq 19
        -- \]
          have qle17 : q ≤ 19 := by
            simp [p11] at hn
            have := hn.2
            simp [mul_add] at this
            by_contra! hqq
            have := aux 11 19 q (by simp) (le_of_lt hqq)
            simp at this
            linarith
          have slt : s ^ 2 < 85 := h3 ▸ (show 2 * p + 3 * q < 85 by linarith)
          replace slt : s < 10 := by
            have : s ^ 2 < 100 := by linarith
            exact lt_of_pow_lt_pow_left' 2 this
          interval_cases q <;> simp [p11] at h3 <;> (interval_cases s <;> try tauto)
    · exact ⟨5, 13, 31, by simp [h]; exact ⟨by decide, by decide, by decide, ⟨7, by simp; decide⟩ ⟩⟩
