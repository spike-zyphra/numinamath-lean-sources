import Mathlib

/- Determine all infinite sequences $(a_1,a_2,...)$ of positive integers satisfying
$a_{n+1}^2 = 1 + (n + 2021)a_n$ for all $n ≥ 1$. -/
theorem algebra_604532 (a : ℕ → ℕ) (a_pos : ∀ n, 0 < a n)
    (ha : ∀ n, a (n + 1) ^ 2 = 1 + (n + 2022) * a n) : a = (· + 2020) := by
  -- Define $b_n = a_n - n$ (subtracing in `ℤ` to avoid having to deal with truncation)
  let b : ℕ → ℤ := fun n ↦ a n - n
  -- If $b_n < 2020$, $b_n < b_{n+1} < 2020$
  have b_lt_bounds : ∀ n, b n < 2020 → b n < b (n + 1) ∧ b (n + 1) < 2020 := fun n hn ↦ by
    unfold b at hn ⊢; constructor
    · -- Suppose that $b_{n+1} ≤ b_n$
      by_contra! h
      -- Then we can rearrange it to $0 ≤ a_n (a_n - n - 2020)$
      replace h := pow_le_pow_left₀ (by omega) (add_le_add_left h (n + 1)) 2
      rw [Nat.cast_add_one, add_sub_cancel, ← Nat.cast_pow, ha n, ← add_rotate, sub_add_cancel,
        ← sub_nonneg, add_comm 1, Nat.cast_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
      have : (a n + 1 : ℤ) ^ 2 - ((n + 2022 : ℤ) * a n + 1) = a n * (a n - n - 2020 : ℤ) := by ring
      rw [this] at h
      -- so $2020 ≤ b_n$, contradicting the original assumption $b_n < 2020$
      replace h := nonneg_of_mul_nonneg_right h (by exact_mod_cast a_pos n)
      rw [sub_nonneg, ← not_lt] at h
      exact h hn
    · -- $b_{n+1} < 2020$ is clear
      rw [sub_lt_iff_lt_add, ← sq_lt_sq₀ (by positivity) (by positivity), ← Nat.cast_pow, ha n]
      norm_cast
      calc
        _ < 1 + (n + 2022) * (n + 2020) := by gcongr; omega
        _ = _ := by ring
  -- $2020 ≤ b_n$ because otherwise `b_lt_bounds` yields a contradiction
  have b_ge : ∀ n, 2020 ≤ b n := fun n ↦ by
    by_contra! h
    have : ∀ k, b n + k ≤ b (n + k) ∧ b (n + k) < 2020 := fun k ↦ by
      induction k with
      | zero => simp [h]
      | succ k ih =>
        specialize b_lt_bounds (n + k) ih.2
        rw [Nat.cast_add_one, ← add_assoc, ← add_assoc, Int.add_one_le_iff]
        exact ⟨ih.1.trans_lt b_lt_bounds.1, b_lt_bounds.2⟩
    specialize this (2020 - b n).toNat
    rw [Int.toNat_sub_of_le h.le, add_sub_cancel] at this
    replace this := this.1.trans_lt this.2
    contradiction
  -- If $2020 < b_n$, $2020 < b_{n+1} < b_n$
  have b_gt_bounds : ∀ n, 2020 < b n → 2020 < b (n + 1) ∧ b (n + 1) < b n := fun n hn ↦ by
    unfold b at hn ⊢; constructor
    · -- $b_{n+1} < 2020$ is clear
      rw [lt_sub_iff_add_lt, ← sq_lt_sq₀ (by positivity) (by positivity), ← Nat.cast_pow, ha n]
      norm_cast
      calc
        _ = 1 + (n + 2022) * (2020 + n) := by ring
        _ < _ := by gcongr; omega
    · -- Suppose that $b_n ≤ b_{n+1}$
      by_contra! h
      -- Then we can rearrange it to $0 ≤ a_n (2020 - (a_n - n))$
      replace h := pow_le_pow_left₀ (by omega) (add_le_add_left h (n + 1)) 2
      rw [Nat.cast_add_one, add_sub_cancel, ← Nat.cast_pow, ha n, ← add_rotate, sub_add_cancel,
        ← sub_nonneg, add_comm 1, Nat.cast_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
      have : ((n + 2022 : ℤ) * a n + 1) - (a n + 1 : ℤ) ^ 2 = a n * (2020 - (a n - n) : ℤ) := by
        ring
      rw [this] at h
      -- so $b_n ≤ 2020$, contradicting the original assumption $2020 < b_n$
      replace h := nonneg_of_mul_nonneg_right h (by exact_mod_cast a_pos n)
      rw [sub_nonneg, ← not_lt] at h
      exact h hn
  -- $b_n ≤ 2020$ because otherwise `b_gt_bounds` yields a contradiction
  have b_le : ∀ n, b n ≤ 2020 := fun n ↦ by
    by_contra! h
    have : ∀ k, 2020 < b (n + k) ∧ b (n + k) ≤ b n - k := fun k ↦ by
      induction k with
      | zero => simp [h]
      | succ k ih =>
        specialize b_gt_bounds (n + k) ih.1
        rw [Nat.cast_add_one, ← add_assoc, ← sub_sub, Int.le_sub_one_iff]
        exact ⟨b_gt_bounds.1, b_gt_bounds.2.trans_le ih.2⟩
    specialize this (b n - 2020).toNat
    rw [Int.toNat_sub_of_le h.le, sub_sub_cancel] at this
    replace this := this.1.trans_le this.2
    contradiction
  -- And thus $b_n = 2020$ for all $n$
  ext n
  have : (a n - n : ℤ) = 2020 := le_antisymm (b_le n) (b_ge n)
  omega
