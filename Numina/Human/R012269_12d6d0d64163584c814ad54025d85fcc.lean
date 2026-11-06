import Mathlib

lemma digits_sum_lt_of_base_le_n {n b : ℕ} (h₁ : 1 < b) (h₂ : b ≤ n) : (Nat.digits b n).sum < n := by
  obtain ⟨k, r, h₃, h₄⟩ := show ∃k r, n = k * b + r ∧ r < b by
    use n / b, n % b
    exact ⟨Eq.symm (Nat.div_add_mod' n b), Nat.mod_lt n (by omega)⟩
  rw [h₃, Nat.digits_eq_cons_digits_div h₁ (by omega), Nat.mul_add_mod_of_lt h₄]
  have h₅ : (k * b + r) / b = k := by exact Nat.div_eq_of_lt_le (by linarith) (by linarith)
  simp only [List.sum_cons, gt_iff_lt, h₅]
  rw [add_comm, add_lt_add_iff_right]
  apply lt_of_le_of_lt (Nat.digit_sum_le b k)
  refine (Nat.lt_mul_iff_one_lt_right ?_).mpr h₁
  rw [←h₅, ←h₃]
  exact Nat.div_pos h₂ (by omega)

lemma pow_mod_10_eq_6_of_mod_10_eq_6 : ∀n ≥ 1, ∀m ≥ 1, n % 10 = 6 → n^m % 10 = 6 := by
  intro n hn₁ m hm₁ hn₂
  obtain ⟨k, hn₃⟩ := show ∃k, n = 10 * k + 6 by
    use n / 10
    omega
  rw [hn₃, Nat.pow_mod, show (10 * k + 6) % 10 = 6 by omega]
  induction' m using Nat.strongRec with m hm
  by_cases hm₂ : m = 1
  · rw [hm₂]
  specialize hm (m - 1) (by omega) (by omega)
  rw [show m = m - 1 + 1 by omega, Nat.pow_add_one, Nat.mul_mod, hm]

/-Given any positive integer, we can write the integer in base 12 and add together the digits of its base 12 representation. We perform this operation on the number $7^{6^{5^{3^{2^{1}}}}}$ repeatedly until a single base 12 digit remains. Find this digit.-/
theorem number_theory_609064 {f : ℕ → ℕ} (hf₁ : ∀n < 12, f n = n) (hf₂ : ∀n ≥ 12, f n = f (Nat.digits 12 n).sum) : f (7^6^5^4^3^2^1) = 4 := by
  have h₁ := Nat.modEq_digits_sum 11 12 (by omega)
  have hf₃ : ∀n, f n ≡ n [MOD 11] := by
    intro n
    induction' n using Nat.strongRec with n ih
    by_cases hn₁ : n < 12
    · rw [hf₁ n hn₁]
    push_neg at hn₁
    have hn₂ : (Nat.digits 12 n).sum < n := by
      apply digits_sum_lt_of_base_le_n
      all_goals omega
    specialize ih (Nat.digits 12 n).sum hn₂
    rw [hf₂ n hn₁]
    apply Nat.ModEq.trans ih
    exact Nat.ModEq.symm (Nat.modEq_digits_sum 11 12 rfl n)
  have hf₄ : ∀n, f n < 12 := by
    intro n
    induction' n using Nat.strongRec with n ih
    by_cases hn₁ : n < 12
    · rw [hf₁ n hn₁]
      exact hn₁
    push_neg at hn₁
    have hn₂ : (Nat.digits 12 n).sum < n := by
      apply digits_sum_lt_of_base_le_n
      all_goals omega
    rw [hf₂ n hn₁]
    exact ih (Nat.digits 12 n).sum hn₂
  suffices f (7 ^ 6 ^ 5 ^ 4 ^ 3 ^ 2 ^ 1) ≡ 4 [MOD 11] by
    rw [Nat.ModEq] at this
    specialize hf₄ (7 ^ 6 ^ 5 ^ 4 ^ 3 ^ 2 ^ 1)
    omega
  apply Nat.ModEq.trans (hf₃ (7 ^ 6 ^ 5 ^ 4 ^ 3 ^ 2 ^ 1))
  have h₂ : ∀ n, 7 ^ n ≡ 4 [MOD 11] ↔ n ≡ 6 [MOD 10] := by
    intro n
    simp only [Nat.ModEq, Nat.reduceMod]
    obtain ⟨k, r, h₁, h₂⟩ := show ∃k r, n = k * 10 + r ∧ r < 10 by
      use n / 10, n % 10
      omega
    rw [h₁, Nat.pow_add, Nat.pow_mul', Nat.mul_mod, Nat.pow_mod, show (k * 10 + r) % 10 = r by omega]
    simp only [Nat.reducePow, Nat.reduceMod, one_pow, Nat.one_mod, one_mul, dvd_refl, Nat.mod_mod_of_dvd]
    interval_cases r <;> norm_num
  rw [h₂, Nat.ModEq]
  apply pow_mod_10_eq_6_of_mod_10_eq_6
  all_goals omega
