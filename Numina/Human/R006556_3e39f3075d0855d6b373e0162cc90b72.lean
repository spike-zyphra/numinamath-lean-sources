import Mathlib
open Finset Nat Real Complex
set_option linter.unusedVariables false
noncomputable section

-- Lemma missing in Lean $4.15$.
lemma Int.cast_eq (x : Int) : Int.cast x = x := rfl

-- Lemma: $ZMod.χ₄ ↑p = (-1)^((p - 1) / 2)$.
lemma zmod_χ₄_eq_neg_one_pow (p : ℕ) (hp : p.Prime) (hp_odd : p % 2 = 1) :
    ZMod.χ₄ ↑p = (-1)^((p - 1) / 2) := by
  have h_p_ne_2 : p ≠ 2 := by
    intro h
    rw [h] at hp_odd
    norm_num at hp_odd
  have h_mod_4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  cases h_mod_4 with
  | inl h_mod_4 =>
    have h_mod_eq_1 : p % 4 = 1 := h_mod_4
    have h_exp_even : (p - 1 : ℕ) / 2 % 2 = 0 := by
      have h_p_mod_4 : p % 4 = 1 := h_mod_eq_1
      have h_p_minus_1_mod_4 : (p - 1 : ℕ) % 4 = 0 := by omega
      have h_exp_mod_2 : (p - 1 : ℕ) / 2 % 2 = 0 := by
        omega
      exact h_exp_mod_2
    have h_χ₄_eq_1 : ZMod.χ₄ ↑p = 1 := by
      rw [ZMod.χ₄_nat_mod_four]
      simp [h_mod_eq_1, hp.ne_zero, hp_odd, Nat.mod_eq_of_lt]
    have h_neg_one_pow_1 : (-1 : ℤ) ^ ((p - 1) / 2 : ℕ) = 1 := by
      have h_exp_mod_2 : (p - 1 : ℕ) / 2 % 2 = 0 := h_exp_even
      have h_pow_eq_1 : (-1 : ℤ) ^ ((p - 1) / 2 : ℕ) = 1 := by
        rw [← Nat.mod_add_div ((p - 1) / 2 : ℕ) 2]
        simp [h_exp_mod_2, pow_add, pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]
      exact h_pow_eq_1
    simp_all
  | inr h_mod_4 =>
    have h_mod_eq_3 : p % 4 = 3 := h_mod_4
    have h_exp_odd : (p - 1 : ℕ) / 2 % 2 = 1 := by
      have h_p_mod_4 : p % 4 = 3 := h_mod_eq_3
      have h_p_minus_1_mod_4 : (p - 1 : ℕ) % 4 = 2 := by omega
      have h_exp_mod_2 : (p - 1 : ℕ) / 2 % 2 = 1 := by
        omega
      exact h_exp_mod_2
    have h_χ₄_eq_neg_1 : ZMod.χ₄ ↑p = -1 := by
      rw [ZMod.χ₄_nat_mod_four]
      simp [h_mod_eq_3, hp.ne_zero, hp_odd, Nat.mod_eq_of_lt]
    have h_neg_one_pow_neg_1 : (-1 : ℤ) ^ ((p - 1) / 2 : ℕ) = -1 := by
      have h_exp_mod_2 : (p - 1 : ℕ) / 2 % 2 = 1 := h_exp_odd
      have h_pow_eq_neg_1 : (-1 : ℤ) ^ ((p - 1) / 2 : ℕ) = -1 := by
        rw [← Nat.mod_add_div ((p - 1) / 2 : ℕ) 2]
        simp [h_exp_mod_2, pow_add, pow_mul, pow_two, mul_assoc, mul_comm, mul_left_comm]
      exact h_pow_eq_neg_1
    simp_all

/-Let $p$ be an odd prime number and let $k$ be an integer such that $p$ does not divide $k$.
Let $\left(\frac{a}{p}\right)$ denote the Legendre symbol. It is given that the Legendre symbol satisfies the following properties:
(i) $\left(\frac{-1}{p}\right) = (-1)^{(p-1)/2}$
(ii) $\left(\frac{ab}{p}\right) = \left(\frac{a}{p}\right)\left(\frac{b}{p}\right)$ for any integers $a, b$.
(iii) If $x$ is an integer not divisible by $p$, then $\left(\frac{x^2}{p}\right) = 1$.
Using these properties, show that $\left(\frac{-k^2}{p}\right) = (-1)^{(p-1)/2}$.-/
theorem number_theory_638457 (p : ℕ) (hp : p.Prime) (hp_odd : p % 2 = 1)
  (k : ℤ) (hk : ¬(p : ℤ) ∣ k) [Fact (Nat.Prime p)]:
  legendreSym p (-k^2) = (-1)^((p - 1) / 2) := by
  -- Step $1$: Use property (ii) to decompose legendreSym $p (-k^2)$.
  have h_step1 : legendreSym p (-k^2) = legendreSym p (-1) * legendreSym p (k^2) := by
    have : (-k^2 : ℤ) = (-1) * k^2 := by
      rw [pow_two, neg_one_mul]
    rw [this, legendreSym.mul]
  -- Step $2$: Use property (i) to obtain legendreSym $p (-1) = (-1)^((p - 1) / 2)$.
  have h_step2 : legendreSym p (-1) = (-1)^((p - 1) / 2) := by
    have h_p_ne_2 : p ≠ 2 := by
      intro h
      rw [h] at hp_odd
      norm_num at hp_odd
    have h_χ₄ : legendreSym p (-1) = ZMod.χ₄ ↑p := by
      exact legendreSym.at_neg_one h_p_ne_2
    rw [h_χ₄]
    exact zmod_χ₄_eq_neg_one_pow p hp hp_odd
  -- Step 3: Use property (iii) to obtain legendreSym $p (k^2) = 1$.
  have h_step3 : legendreSym p (k^2) = 1 := by
    have : k ≠ 0 := by
        contrapose! hk
        rw [hk, ← Int.cast_zero]
        exact dvd_zero _
    have : ↑k ≠ (0 : ZMod p) := by
      by_contra h
      have : (p : ℤ) ∣ k := by
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd k p).mp h
      contradiction
    exact legendreSym.sq_one' p this
  -- Step $4$: Substitute the results.
  have h_step4 : legendreSym p (-k^2) = (-1)^((p - 1) / 2) * 1 := by
    rw [h_step1, h_step2, h_step3]
  -- Conclusion.
  rw [h_step4, mul_one]
