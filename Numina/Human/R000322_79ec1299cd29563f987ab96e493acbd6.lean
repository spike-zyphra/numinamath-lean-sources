import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Prove that among the numbers of the form  $ 50^n \plus{} (50n\plus{}1)^{50}$ ,
where  $ n$  is a natural number, there exist infinitely many composite numbers.-/
theorem number_theory_8925 :
  ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ¬ Nat.Prime (50^n + (50 * n + 1)^50) := by
  intro N
  -- We can choose large enough k such that 6k+3 > N
  rcases Archimedean.arch N <| show 0 < 6 by norm_num with ⟨k, hk⟩
  set n := 6*k+3 with hn
  use n
  constructor
  -- show 6k+3 > N
  . dsimp at hk; linarith
  -- Suffices to show 3 divides 50^n + (50 * n + 1)^50.
  suffices 3 ∣ 50^n + (50 * n + 1)^50 by
    have : 50 < 50^n + (50 * n + 1)^50 := by
      have : 50^1 < 50^n := by
        rw [Nat.pow_lt_pow_iff_right (by norm_num)]
        linarith
      have : 0 < (50*n+1)^50 := by
        apply Nat.pow_pos
        linarith
      linarith
    rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)]
    use 3
    split_ands
    . assumption
    . norm_num
    . linarith
  --  - \( 50n + 1 \equiv 2n + 1 \ (\text{mod}\ 3) \). Thus, \( (50n + 1)^{50} \equiv (2n + 1)^{50} \ (\text{mod}\ 3) \).
  --  - The expression becomes \( 2^n + (2n + 1)^{50} \ (\text{mod}\ 3) \).
  have h50n_add_one : 50*n+1 ≡ 1 [MOD 3] := by
    rw [hn, show 50*(6*k+3)=3*(50*(2*k+1)) by ring, Nat.ModEq,
      Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul]
  replace h50n_add_one := Nat.ModEq.pow 50 h50n_add_one
  rw [Nat.one_pow] at h50n_add_one
  -- - \( 50 \equiv 2 \ (\text{mod}\ 3) \),
  have h50 : 50 ≡ 2 [MOD 3] := by decide
  -- so \( 50^n \equiv 2^n \ (\text{mod}\ 3) \).
  replace h50 := Nat.ModEq.pow n h50
  -- - Let \( n = 3k \) where \( k \) is a natural number.
  --  - Then, \( 2^{3k} \equiv (2^3)^k \equiv 2^k \ (\text{mod}\ 3) \).
  --  - \( 2n + 1 = 6k + 1 \equiv 1 \ (\text{mod}\ 3) \), so \( (2n + 1)^{50} \equiv 1 \ (\text{mod}\ 3) \).
  --  - For \( k \) odd, \( 2^k \equiv 2 \ (\text{mod}\ 3) \).
  conv_rhs at h50 =>
    rw [hn, show 6*k+3=2*(3*k+1)+1 by ring, Nat.pow_add, Nat.pow_mul]
  have h : 2^2 ≡ 1 [MOD 3] := by decide
  replace h := Nat.ModEq.pow (3*k+1) h
  replace h := Nat.ModEq.mul_right (2^1) h
  rw [Nat.one_pow, Nat.one_mul, Nat.pow_one] at h
  replace h50 := Nat.ModEq.trans h50 h
  -- Thus, \( 2^k + 1 \equiv 0 \ (\text{mod}\ 3) \).
  have := Nat.ModEq.add h50 h50n_add_one
  rwa [Nat.ModEq, Nat.mod_self, ← Nat.dvd_iff_mod_eq_zero] at this
