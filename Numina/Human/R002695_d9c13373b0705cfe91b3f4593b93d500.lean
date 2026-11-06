import Mathlib

open Nat

-- Show that if 0 < a < b ≤ c then a * b divides c!.
theorem lemma_1 {a b c : ℕ} (ha0 : 0 < a) (hab : a < b) (hc : b ≤ c) : a * b ∣ c ! := by
  -- We have c! = (b - 1)! * b * (b + 1).ascFactorial (c - b).
  rw [show c = (b - 1 + 1) + (c - b) by omega, ← factorial_mul_ascFactorial]
  rw [factorial_succ, show b - 1 + 1 = b by omega, mul_comm, mul_assoc]
  -- It is enough to show that a ∣ (b - 1)! * (b + 1).ascFactorial (c - b).
  apply Nat.mul_dvd_mul_left
  -- We have a ∣ (b - 1)! (because a ≤ b - 1), so a ∣ (b - 1)! * x for any x.
  have ⟨k, hk⟩ : a ∣ (b - 1)! := dvd_factorial ha0 (by omega)
  use k * (b + 1).ascFactorial (c - b)
  rw [hk]
  ring

-- Show that if p is prime and 5 < p, then (p - 1)^2 divides (p - 1)!.
lemma lemma_2 {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) : (p - 1)^2 ∣ (p - 1)! := by
  -- We have (p - 1)! = (p - 2)! * (p - 1).
  have eq : (p - 1)! = (p - 2)! * (p - 1) := by
    rw [show p - 1 = (p - 2) + 1 by omega, factorial_succ, mul_comm]
  rw [pow_two, eq]
  -- It is left to show that p - 1 ∣ (p - 2)!.
  apply Nat.mul_dvd_mul_right
  -- We have p - 1 = 2 * ((p - 1) / 2).
  replace eq : p - 1 = 2 * ((p - 1) / 2) := by
    -- It is enough to show that p is odd.
    suffices Odd p by
      rw [← Nat.two_mul_div_two_add_one_of_odd this]
      omega
    -- p is odd because p is prime and p ≠ 2.
    apply hp.odd_of_ne_two
    linarith
  rw [eq]
  -- We have 2 < (p - 1) / 2 ≤ p - 2, so we can apply lemma_1 and prove that
  -- 2 * ((p - 1) / 2) = p - 1 divides (p - 2)!.
  apply lemma_1 zero_lt_two (by omega) (by omega)

-- Show that p! ≤ p^(p - 1) for all p.
lemma lemma_3 (p : ℕ) : p ! ≤ p ^ (p - 1) := by
  -- Proof by induction.
  induction p with
  -- 0! = 1 ≤ 1 = 0^0.
  | zero => simp
  | succ p ih =>
    -- Suppose that p! ≤ p^(p - 1) and show that (p + 1)! ≤ (p + 1)^(p + 1 - 1).
    by_cases hp : p = 0
    · -- If p = 0 then 1! = 1 ≤ 1 = 1^1.
      simp [hp]
    -- We have (p + 1)^(p + 1 - 1) = (p + 1)^(p - 1) * (p + 1) and (p + 1)! = p! * (p + 1).
    rw [Nat.factorial_succ, show p + 1 - 1 = (p - 1) + 1 by omega, pow_add, mul_comm, pow_one]
    gcongr
    -- It is left to show that p! ≤ (p + 1)^(p - 1).
    -- We have p! ≤ p^(p - 1) ≤ (p + 1)^(p - 1).
    apply le_trans ih
    apply pow_le_pow (by linarith) (by linarith) (le_refl _)

/- What are the pairs of natural integers $(n, p)$, such that $(p-1)!+1=p^{n}$? -/
theorem number_theory_101229 (n p : ℕ) :
    ((p - 1)! + 1 = p ^ n) ↔ (n = 1 ∧ p = 2) ∨ (n = 1 ∧ p = 3) ∨ (n = 2 ∧ p = 5) := by
  symm
  constructor
  · -- Show that (n, p) = (1, 2), (1, 3), (2, 5) satisfy the equation
    -- (p - 1)! + 1 = p^n.
    intro h
    rcases h with ⟨hn, hp⟩ | ⟨hn, hp⟩ | ⟨hn, hp⟩ <;> (subst n p; norm_num [Nat.factorial_succ])
  intro h
  -- Show that n ≠ 0.
  have hn : n ≠ 0 := by
    contrapose! h
    simp [h]
    -- If n = 0 then (p - 1)! + 1 = 1, so (p - 1)! = 0.
    -- On the other hand x! ≠ 0 for any x ∈ ℕ, a contradiction.
    exact Nat.factorial_ne_zero _
  -- Show that p is prime.
  have hp : p.Prime := by
    -- Apply Wilson's theorem to show that p is prime.
    apply Nat.prime_of_fac_equiv_neg_one
    · -- We need to show that (p - 1)! = -1 (mod p).
      -- Consider (p - 1)! + 1 = p^n (mod p).
      apply_fun (fun n : ℕ => (n : ZMod p)) at h
      -- We get (p - 1)! + 1 = 0 (mod p), so (p - 1)! = -1 (mod p).
      simp [hn] at h
      linear_combination h
    · -- We also need to show that p ≠ 1.
      -- If p = 1 then (p - 1)! + 1 = 2 ≠ 1 = 1^n.
      contrapose! h
      subst p
      norm_num
  -- Consider two cases p ≤ 5 and 5 < p.
  by_cases hp5 : p ≤ 5
  · -- If p ≤ 5 then p = 2 or p = 3 or p = 5.
    replace hp5 : p = 2 ∨ p = 3 ∨ p = 5 := by
      interval_cases p <;> norm_num at hp <;> simp
    rcases hp5 with ⟨rfl⟩ | ⟨rfl⟩ | ⟨rfl⟩ <;> norm_num [Nat.factorial_succ] at h <;> simp
    · -- If p = 2 then we get 2 = 2 ^ n, so n = 1.
      nth_rw 1 [show 2 = 2 ^ 1 by norm_num] at h
      apply Nat.pow_right_injective (le_refl _) at h
      exact h.symm
    · -- If p = 3 then we get 3 = 3 ^ n, so n = 1.
      nth_rw 1 [show 3 = 3 ^ 1 by norm_num] at h
      apply Nat.pow_right_injective (by linarith) at h
      exact h.symm
    · -- If p = 5 then we get 25 = 5 ^ n, so n = 2.
      nth_rw 1 [show 25 = 5 ^ 2 by norm_num] at h
      apply Nat.pow_right_injective (by linarith) at h
      exact h.symm
  -- Suppose that 5 < p and show that this case is impossible.
  simp at hp5
  -- Prove that p - 1 divides ∑ i ∈ Finset.range n, p^i.
  have hdvd : p - 1 ∣ ∑ i ∈ Finset.range n, p^i := by
    -- lemma_2 implies that (p - 1)! = (p - 1)^2 * k for some k.
    have ⟨k, hk⟩ := lemma_2 hp hp5
    -- Show that ∑ i ∈ Finset.range n, p^i = (p - 1) * k.
    use k
    -- Multiply both sides by p - 1 and get
    -- (p - 1) * ∑ i ∈ Finset.range n, p^i = p^n - 1
    --         = (p - 1)! (from h)
    --         = (p - 1)^2 * k.
    apply Nat.mul_left_cancel (show 0 < p - 1 by omega)
    rw [← mul_assoc, ← pow_two, ← hk]
    zify [show 1 < p by linarith] at h ⊢
    rw [mul_geom_sum]
    linarith
  -- Prove that p - 1 divides n.
  replace hdvd : p - 1 ∣ n := by
    -- Show that n ≡ 0 [MOD p - 1].
    rw [← Nat.modEq_zero_iff_dvd]
    calc
      -- We have n ≡ ∑ i ∈ Finset.range n, 1 [MOD p - 1].
      n ≡ ∑ i ∈ Finset.range n, 1 [MOD p - 1] := by
        simp [Nat.mod_self]
        rfl
      -- Show that p^i ≡ 1 [MOD p - 1] for all i.
      _ ≡ ∑ i ∈ Finset.range n, p^i [MOD p - 1] := by
        rw [Nat.ModEq.eq_1]
        nth_rw 2 [Finset.sum_nat_mod]
        congr
        ext i
        rw [Nat.pow_mod]
        have h1 : 1 % (p - 1) = 1 := by
          rw [show p - 1 = (p - 3) + 2 by omega, Nat.one_mod]
        suffices p % (p - 1) = 1 by rw [this, one_pow, h1]
        nth_rw 1 [show p = (p - 1) + 1 by omega]
        rw [Nat.add_mod, Nat.mod_self, h1, zero_add, h1]
      -- We get n ≡ ∑ i ∈ Finset.range n, p^i [MOD p - 1]
      --          ≡ 0 [MOD p - 1] (because p - 1 divides ∑ i ∈ Finset.range n, p^i).
      _ ≡ 0 [MOD p - 1] := by
        rw [Nat.modEq_zero_iff_dvd]
        exact hdvd
  -- Show that (p - 1)! + 1 < p^n.
  contrapose! h
  apply Nat.ne_of_lt
  calc
    -- We have (p - 1)! + 1 < p!.
    (p - 1)! + 1 < p ! := by
      nth_rw 2 [show p = (p - 1) + 1 by omega]
      rw [Nat.factorial_succ, add_mul, one_mul]
      nth_rw 1 [← one_mul (p - 1)!]
      gcongr
      · omega
      · rw [one_lt_factorial]
        omega
    -- lemma_3 implies that p! ≤ p^(p - 1).
    _ ≤ p ^ (p - 1) := lemma_3 p
    -- p - 1 divides n and n ≠ 0, so p - 1 ≤ n and p^(p - 1) ≤ p^n.
    _ ≤ p ^ n := by
      rw [Nat.pow_le_pow_iff_right (by omega)]
      apply Nat.le_of_dvd (by omega) hdvd