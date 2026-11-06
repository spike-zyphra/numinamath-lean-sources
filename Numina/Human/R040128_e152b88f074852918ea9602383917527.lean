import Mathlib

/-3. Suppose that $a, b$ and $c$ are positive integers with $2^{a} 3^{b} 5^{c}=36000$. What is the value of $3 a+4 b+6 c$ ?-/
theorem number_theory_263018 (a b c : ℕ) (h : 2^a * 3^b * 5^c = 36000) :
    3 * a + 4 * b + 6 * c = 41 := by
-- Prepare to use `padicValNat`
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
-- Rewrite $36000$ as a product of prime powers and apply `padicValNat` to find the values of $a$, $b$ and $c$
  rw [show 36000 = 2^5 * 3^2 * 5^3 by simp] at h
  let pv2 := h; apply_fun fun t => padicValNat 2 t at pv2
  repeat rw [padicValNat.mul] at pv2
  repeat rw [padicValNat.prime_pow, padicValNat_prime_prime_pow, padicValNat_prime_prime_pow] at pv2
  simp at pv2
  let pv3 := h; apply_fun fun t => padicValNat 3 t at pv3
  repeat rw [padicValNat.mul] at pv3
  repeat rw [padicValNat_prime_prime_pow, padicValNat.prime_pow, padicValNat_prime_prime_pow] at pv3
  simp at pv3
  let pv5 := h; apply_fun fun t => padicValNat 5 t at pv5
  repeat rw [padicValNat.mul] at pv5
  repeat rw [padicValNat.prime_pow, padicValNat_prime_prime_pow, padicValNat_prime_prime_pow] at pv5
-- The goal follows from `pv2`, `pv3` and `pv5`
  simp at pv5; any_goals omega
  all_goals positivity