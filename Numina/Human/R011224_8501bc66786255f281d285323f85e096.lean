import Mathlib

/- 1. If $a, b$, and $c$ are natural numbers such that the numbers
$$
24^{a}+2^{b}+2018^{c} \quad \text { and } \quad 10^{c}+3^{a}+2018^{b}
$$
are divisible by 7, prove that the number $30^{b}+3^{c}+2018^{a}$ is not divisible by 7. -/
theorem number_theory_104732 (a b c : ℕ)
    (h1 : 7 ∣ 24^a + 2^b + 2018^c)
    (h2 : 7 ∣ 10^c + 3^a + 2018^b) :
    ¬7 ∣ 30^b + 3^c + 2018^a := by
  -- Assume that 7 ∣ 30^b + 3^c + 2018^a and derive a contradiction.
  intro h
  -- Rewrite all assumptions as equalities over ℤ_7:
  -- h1 : 3^a + 2^b + 2^c = 0 (mod 7)
  -- h2 : 3^c + 3^a + 2^b = 0 (mod 7)
  -- h  : 2^b + 3^c + 2^a = 0 (mod 7)
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at h1 h2 h
  push_cast at h1 h2 h
  reduce_mod_char at h1 h2 h
  -- 7 is a prime number.
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  -- 2 ≠ 0 (mod 7) and 3 ≠ 0 (mod 7).
  have h2_0 : (2 : ZMod 7) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
  have h3_0 : (3 : ZMod 7) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
  -- Show that a ^ n = a ^ (n % 6) (mod 7) for any a ≠ 0 (mod 7).
  have hpow {a : ZMod 7} (ha : a ≠ 0) n : a ^ n = a ^ (n % 6) := by
    -- It is enough to show that a ^ 6 = 1 (mod 7).
    apply pow_eq_pow_mod
    -- This follows from the fact that 7 is prime and Fermat's Little Theorem: a^(p - 1) = 1 (mod p).
    exact ZMod.pow_card_sub_one_eq_one ha
  -- Prove that 3^n - 2^n = 0 (mod 7) implies that 3^n = 2^n = 1 (mod 7).
  have h6 n (hn : (3 ^ n - 2 ^ n : ZMod 7) = 0) : 3 ^ n = (1 : ZMod 7) ∧ 2 ^ n = (1 : ZMod 7) := by
    -- It is enough to show that 3^n = 1 (mod 7) because 3^n - 2^n = 0 implies 2^n = 3^n (mod 7).
    suffices 3 ^ n = (1 : ZMod 7) by
      simp [this] at hn ⊢
      linear_combination -hn
    -- We have 3^(n % 6) - 2^(n % 6) = 0 and we need to show that 3^(n % 6) = 1.
    rw [hpow h3_0] at hn ⊢
    rw [hpow h2_0] at hn
    -- Consider all possible values of n % 6 and show that only n % 6 = 0 yields 3^(n%6) - 2^(n%6) = 0.
    mod_cases h : n % 6 <;> (rw [Nat.ModEq.eq_1] at h; rw [h] at hn ⊢; norm_num at hn ⊢)
    all_goals {
      contrapose! hn
      exact Ne.symm (ne_of_beq_false rfl)
    }
  -- Subtract h1 from h2 and get 3^c - 2^c = 0 (mod 7).
  have hc : 3 ^ c - 2 ^ c = (0 : ZMod 7) := by linear_combination h2 - h1
  -- Subtract h from h2 and get 3^a - 2^a = 0 (mod 7).
  have ha : 3 ^ a - 2 ^ a = (0 : ZMod 7) := by linear_combination h2 - h
  -- 3^c - 2^c = 0 implies that 3^c = 1 (mod 7).
  -- 3^a - 2^a = 0 implies that 2^a = 1 (mod 7).
  -- Rewrite h as follows:
  -- 2^b + 1 + 1 = 0 or 2^b = 5 (mod 7).
  rw [(h6 _ hc).1, (h6 _ ha).2] at h
  -- All possible values of 2^b (mod 7) are 1, 2, and 4.
  have hpow2 n : (2 : ZMod 7) ^ n ∈ [1, 2, 4] := by
    rw [hpow h2_0]
    mod_cases hn : n % 6 <;> (rw [Nat.ModEq.eq_1] at hn; rw [hn]; reduce_mod_char; simp)
  simp at hpow2
  -- Consider all possible values of 2^b and conclude that 2^b ≠ 5 (mod 7).
  rcases hpow2 b with h2 | h2 | h2 <;> (contrapose! h; rw [h2]; exact Ne.symm (ne_of_beq_false rfl))