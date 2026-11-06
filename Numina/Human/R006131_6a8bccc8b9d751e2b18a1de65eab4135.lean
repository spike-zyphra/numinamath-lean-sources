import Mathlib

set_option linter.dupNamespace false

namespace number_theory_619280

lemma exponent_dvd_of_prime_pow_eq_pow {p a m n : ℕ} (p_prime : p.Prime) (pow_eq : p ^ m = a ^ n) : n ∣ m := by
  have factorization_eq := congrArg Nat.factorization pow_eq
  rw [Nat.Prime.factorization_pow p_prime, Nat.factorization_pow] at factorization_eq
  --have := congrFun factorization_eq p
  --have := Finsupp.congr_fun factorization_eq p
  have := congrFun (congrArg DFunLike.coe factorization_eq) p
  simp at this
  exact Dvd.intro (a.factorization p) this.symm

lemma ex_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow
    {p a m n : ℕ} (p_prime : p.Prime) (n_nonzero : n ≠ 0) (pow_eq : p ^ m = a ^ n) :
    ∃ k, a = p ^ k := by
  have := exponent_dvd_of_prime_pow_eq_pow p_prime pow_eq
  rcases this with ⟨k, m_eq⟩
  rw [m_eq] at pow_eq
  use k
  rw [show p ^ (n * k) = (p ^ k) ^ n by ring] at pow_eq
  have := Nat.pow_left_injective n_nonzero
  exact this pow_eq.symm

/-
Given integers $a$ and $b$, and a prime number $p$ such that:
$$p^{2017^p + p} = a^{2017b}$$
Find the minimum value of $a^p$.
 -/
theorem number_theory_619280 :
    IsLeast {a ^ p | (a : ℕ) (b : ℕ) (p : ℕ) (hp : p.Prime) (h : p ^ (2017 ^ p + p) = a ^ (2017 * b))} (2017 ^ 2017) := by
  have prime_2017 : Nat.Prime 2017 := by
    native_decide
  have : {a ^ p | (a : ℕ) (b : ℕ) (p : ℕ) (hp : p.Prime) (h : p ^ (2017 ^ p + p) = a ^ (2017 * b))} =
      {a ^ 2017 | (a : ℕ) (b : ℕ) (h : 2017 ^ (2017 ^ 2017 + 2017) = a ^ (2017 * b))} := by
    ext a_pow_p
    constructor
    . simp
      rintro a b p h hp rfl
      have : p = 2017 := by
        --  1. We start with the given equation: $p^{2017^p + p} = a^{2017b}$.
        --  2. To satisfy the equation, we need $2017$ to divide $2017^p + p$. This implies $2017 \mid 2017^p + p$.
        have : 2017 ∣ 2017 ^ p + p := by
          -- This can be moved out and shared for proving `∃ e, a = p ^ e` in the last step, but it's too much work with the current structure.
          have right_pow_dvd_left_pow : 2017 * b ∣ 2017 ^ p + p := by
            exact exponent_dvd_of_prime_pow_eq_pow hp h
          exact dvd_of_mul_right_dvd right_pow_dvd_left_pow
        --  3. Since $2017$ is a prime number, the only way for $2017$ to divide $2017^p + p$ is if $p = 2017$.
        have : 2017 ∣ p := by
          have : 2017 ∣ 2017 ^ p := by
            refine dvd_pow_self 2017 ?_
            exact hp.ne_zero
          omega
        --generalize 2017 = n at this
        have : 2017 = 1 ∨ 2017 = p := by
          exact (Nat.dvd_prime hp).mp this
        simp at this
        exact this.symm
      --  4. Substituting $p = 2017$ into the equation, we get: $2017^{2017^{2017} + 2017} = a^{2017b}$.
      subst this
      simp
      use b
    . simp
      rintro a b h_substituted rfl
      use a, b, 2017
      --generalize 2017 ^ (2017 ^ 2017 + 2017) = left at h_substituted
      /-
      constructor
      . exact h_substituted
      constructor
      . native_decide
      . rfl
       -/
  rw [this]
  --  5. Simplifying the exponent on the left side, we have: $2017^{2017^{2017} + 2017} = 2017^{2017(2017^{2016} + 1)}$.
  have : 2017 ^ (2017 ^ 2017 + 2017) = 2017 ^ (2017 * (2017 ^ 2016 + 1)) := by
    generalize h : 2017 = _2017
    congr
    rw [← h]
    simp --dsimp
    ring
  --  6. Therefore, the equation becomes: $2017^{2017(2017^{2016} + 1)} = a^{2017b}$.
  rw [this]
  clear this
  --  7. To minimize $a$, we maximize $b$. The maximum value of $b$ is $2017^{2016} + 1$.
  --  8. Substituting $b = 2017^{2016} + 1$ into the equation, we get: $2017^{2017(2017^{2016} + 1)} = a^{2017(2017^{2016} + 1)}$.
  --  9. This implies $a = 2017$.
  -- 10. The minimum value of $a^p$ is then $2017^{2017}$.
  -- 11. Therefore, the minimum value of $a^p$ is \\boxed{2017^{2017}}.
  constructor
  . simp
  . simp [lowerBounds]
    rintro a_pow_p a b h rfl
    generalize _2017_eq : 2017 = _2017 at h prime_2017
    suffices _2017 ≤ a by
      clear h
      exact Nat.pow_le_pow_of_le_left this _2017
    have : _2017 ^ (_2017 * (_2017 ^ 2016 + 1)) ≠ 1 := by
      --rw [← _2017_eq] at h
      have gt_1 : _2017 > 1 := by
        linarith
      suffices _2017 ^ (_2017 * (_2017 ^ 2016 + 1)) > 1 by
        omega
      suffices _2017 * (_2017 ^ 2016 + 1) ≠ 0 by
        exact Nat.one_lt_pow this gt_1
      simp
      linarith
    have : ∃ n, a = _2017 ^ n := by
      have : _2017 * b ≠ 0 := by
        have : b ≠ 0 := by
          rintro rfl
          simp at h
          contradiction
        rw [← _2017_eq]
        omega
      exact ex_k_base_eq_p_pow_k_of_prime_p_pow_eq_base_pow prime_2017 this h
    rcases this with ⟨n, rfl⟩
    by_cases w_n_eq_0 : n = 0
    . exfalso
      subst w_n_eq_0
      simp at h
      contradiction
    exact Nat.le_self_pow w_n_eq_0 _2017

end number_theory_619280
open number_theory_619280
