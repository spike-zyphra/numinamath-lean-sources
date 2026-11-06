import Mathlib

/- Lemma 5.1 if `d | n` then `2^d-1 | 2^n-1` -/
theorem aux_4811 {d n : ℕ} (h : d ∣ n) : 2^d - 1 ∣ 2^n - 1 := by
  rcases h with ⟨k, rfl⟩
  have : 0 < 2^d := by apply Nat.pow_pos; norm_num
  have : 0 < (2^d)^k := by apply Nat.pow_pos this
  have := sub_one_dvd_pow_sub_one ((2^d) : ℤ) k
  rw [pow_mul, ← Nat.modEq_iff_dvd' (by omega), Nat.modEq_iff_dvd]
  rw [Nat.cast_sub (by omega)]
  push_cast
  assumption

/- `f n` are all pseudoprimes -/
def f_4811 : ℕ → ℕ
  | 0 => 341
  | n+1 => 2^(f_4811 n) - 1

/- Show that there are infinitely many pseudoprimes to the base 2.-/
theorem number_theory_4811 : Set.Infinite {n : ℕ | Nat.FermatPsp n 2} := by
  -- denote the set of pseudoprimes to the base 2 as `S`
  set S : Set ℕ := {n : ℕ | Nat.FermatPsp n 2}
  have hf0 : f_4811 0 = 341 := rfl
  have hfsucc n : f_4811 (n+1) = 2^f_4811 n - 1 := rfl
  have : StrictMono f_4811 := by
    apply strictMono_nat_of_lt_succ
    intro n
    induction' n with n ih
    . rw [hfsucc, hf0]; norm_num
    rw [hfsucc n, hfsucc (n+1)]
    suffices 2^f_4811 n < 2^f_4811 (n+1) by
      refine Nat.sub_lt_sub_right ?_ this
      have : 0 < 2^f_4811 n := by apply Nat.pow_pos; norm_num
      omega
    exact Nat.pow_lt_pow_right (by norm_num) ih
  have hfinj : Function.Injective f_4811 := StrictMono.injective this
  -- suffices to show that `f n` are all pseudoprimes
  refine Set.infinite_of_injective_forall_mem hfinj (fun n : ℕ => ?_)
  simp [f_4811, S]
  -- use mathematical induction
  induction' n with n ih
  -- check that `f 0 = 341` is pseudoprime
  . simp [f_4811]
    unfold Nat.FermatPsp Nat.ProbablePrime
    norm_num
  -- check that `f (n + 1)` is pseudoprime
  have : 0 < 2^(f_4811 n - 1) := by apply Nat.pow_pos; norm_num
  simp [f_4811]
  unfold Nat.FermatPsp Nat.ProbablePrime at ih ⊢
  have one_lt_fn n : 1 < f_4811 n := by
    induction' n with n ih
    . simp [f_4811]
    simp [f_4811]
    have := Nat.pow_lt_pow_of_lt (show 1 < 2 by norm_num) ih
    omega
  have : 2^1 < 2^f_4811 n := by apply Nat.pow_lt_pow_right; norm_num; exact one_lt_fn n
  -- use induction hypothese `f(n) | 2^(f(n)-1) - 1`
  -- to conclude `f(n) | 2^f(n) - 2`
  have hfn : f_4811 n ∣ 2^(f_4811 n - 1) - 1 := ih.1
  rw [← Nat.modEq_iff_dvd' (by omega)] at hfn
  replace hfn := Nat.ModEq.mul_left 2 hfn
  rw [mul_one, mul_comm, ← pow_succ, show f_4811 n - 1 + 1 = f_4811 n by omega, Nat.modEq_iff_dvd' (by omega)] at hfn
  rw [show 2^f_4811 n - 1 -1 = 2^f_4811 n - 2 by omega]
  -- use Lemma 5.1 to show 2^(m-1) = 1 mod m, where m=2^f(n)-1
  refine ⟨aux_4811 hfn, ?_, ?_⟩
  have fn_comp := ih.2.1
  rw [Nat.not_prime_iff_exists_dvd_lt (by omega)] at fn_comp ⊢
  rcases fn_comp with ⟨m, fn_comp⟩
  use 2^m-1
  split_ands
  -- use Lemma 5.1 to show 2^f(n)-1 is composite number
  . exact aux_4811 fn_comp.1
  . have : 2 ≤ m := fn_comp.2.1
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
    omega
  . suffices 2^m < 2^f_4811 n by
      refine Nat.sub_lt_sub_right ?_ this
      have : 0 < 2^m := by apply Nat.pow_pos; norm_num
      omega
    exact Nat.pow_lt_pow_right (by norm_num) fn_comp.2.2
  -- check that 1 < 2^f(n)-1
  . suffices 2 < 2 ^ f_4811 n by omega
    nth_rw 1 [← pow_one 2]
    exact Nat.pow_lt_pow_of_lt (by norm_num) (one_lt_fn n)
