import Mathlib

open Finset Nat

-- If two pairs of natural numbers have the same sum, then they have the same difference
lemma l_sublemma {p q r s : ℕ} (h : p ≤ r) (h' : p + q = r + s) :
    q - s = r - p := by
  rw [← add_left_inj s, ← add_left_inj p, Nat.sub_add_cancel (by linarith), add_assoc, ← Nat.sub_add_comm h, ← add_assoc, Nat.add_sub_cancel_right]
  linarith

-- If b ≤ a and the exponents add up to the same value, then the side with a larger a exponent is larger
lemma l_key {a b : ℝ} {p q r s : ℕ} (ha : 0 < a) (hb : 0 < b) (h : b ≤ a) (h' : p ≤ r) (h'' : p + q = r + s) :
    a ^ p * b ^ q ≤ a ^ r * b ^ s := by
  calc
    a ^ p * b ^ q = (a ^ r / a ^ (r - p)) * (b ^ s * b ^ (q - s)) := by
      congr
      · rw [pow_sub₀ a (by positivity) h', ← div_div, div_self (by positivity)]
        simp
      rw [← pow_add]
      congr
      exact (add_sub_of_le (by linarith)).symm
    _ = (a ^ r * b ^ s) * (b ^ (q - s) / (a ^ (r - p))) := by ring
    _ ≤ a ^ r * b ^ s := by
      apply mul_le_of_le_one_right (by positivity)
      rw [div_le_one (by positivity), show q - s = r - p by exact l_sublemma h' h'']
      gcongr

/- 3. Prove that for all positive numbers $a$ and $b$, the inequality $\left(a^{2018}+b^{2018}\right)^{2019}>\left(a^{2019}+b^{2019}\right)^{2018}$ holds. -/
theorem inequalities_286178 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a ^ 2018 + b ^ 2018) ^ 2019 > (a ^ 2019 + b ^ 2019) ^ 2018 := by
  -- By symmetry, we can assume that b ≤ a
  wlog h : b ≤ a
  · -- Follows by just commuting terms
    specialize this b a hb ha (by linarith)
    rw [add_comm, add_comm (a ^ _)]
    tauto
  -- Expand using the binomial theorem
  repeat rw [add_pow]
  -- Remove edge terms
  rw [range_eq_Ico, sum_Ico_succ_top (by norm_num), sum_eq_sum_Ico_succ_bot (by norm_num)]
  conv_rhs => rw [sum_Ico_succ_top (by norm_num)];
  simp
  repeat rw [← pow_mul]
  rw [show 1 = 0 + 1 by norm_num]
  nth_rw 5 [show 2019 = 2018 + 1 by norm_num]
  rw [← sum_Ico_add, ← range_eq_Ico, mul_comm 2019]
  -- Cancel the a ^ (2018 * 2019) term
  apply add_lt_add_right
  -- We will show the RHS sum is greater than the LHS sum
  apply lt_add_of_pos_of_lt (by positivity)
  apply sum_lt_sum
  · -- Show that the summands are ordered
    intro i hi
    apply mul_le_mul
    · -- Show that the monomials satisfy an inequality
      repeat rw [← pow_mul]
      simp at hi
      apply l_key ha hb h (by linarith)
      repeat rw [← mul_add]
      repeat rw [Nat.add_sub_cancel' (by linarith)]
    · -- Show that choose 2018 i ≤ choose 2019 (i + 1) by Pascal's identity
      simp
      rw [show 2019 = 2018 + 1 by norm_num, add_comm 1, choose_succ_succ']
      linarith
    · -- Show that choose 2018 i is nonnegative
      positivity
    -- Show that choose 2018 i is nonnegative
    positivity
  -- Show that the inequality is strict by providing a specific example
  use 0
  simp
  repeat rw [← pow_mul]
  -- Using the fact b ≤ a, we can prove a strict bound
  calc
    b ^ (2019 * 2018) = b ^ 2018 * b ^ (2018 * 2018) := by ring
    _ ≤ a ^ 2018 * b ^ (2018 * 2018) := by gcongr
    _ < _ := by apply lt_mul_right; positivity; norm_num