import Mathlib

-- Show that Even (a / 10 % 10) is equivalent to Even (a / 10)
-- for any natural number 10.
lemma lemma_1 (a : ℕ) : Even (a / 10 % 10) ↔ Even (a / 10) := by
  -- We have Even (n % a) ↔ Even n for all even a.
  rw [Even.mod_even_iff]
  -- 10 is even.
  decide

/- Prove that every power of 3 , from 27 onward, has an even tens digit. -/
theorem number_theory_256910 (n : ℕ) :
    3^n ≥ 27 → Even ((3^n) / 10 % 10) := by
  intro h
  -- 3^n ≥ 27 iff 3 ≤ n.
  replace h : 3 ≤ n := by
    rw [show 27 = 3^3 by norm_num] at h
    rwa [ge_iff_le, Nat.pow_le_pow_iff_right (by norm_num)] at h
  -- We need to show that 3^n / 10 is even (from lemma_1).
  rw [lemma_1]
  -- Show that 3^n % 10 ∈ [1, 3, 7, 9] for any n.
  have h3 n : 3 ^ n % 10 ∈ [1, 3, 7, 9] := by
    clear h
    -- Proof by induction.
    induction n with
    -- 3^0 = 1.
    | zero => simp
    | succ n ih =>
      -- Assume that 3^n % 10 ∈ [1, 3, 7, 9].
      -- We have 3^(n + 1) % 10 = 3^n * 3 % 10 ∈ [3, 9, 21 % 10, 27 % 10] = [3, 9, 1, 7].
      simp [pow_succ, Nat.mul_mod] at ih ⊢
      rcases ih with h | h | h | h <;> rw [h] <;> norm_num
  -- Proof by induction.
  induction n with
  -- If n = 0 then ¬ 3 ≤ 0.
  | zero => norm_num at h
  | succ n ih =>
    -- Assume that 3 ≤ n implies that Even (3^n / 10).
    -- Show that 3 ≤ n + 1 implies that Even(3^(n + 1) / 10).
    cases' show n = 2 ∨ 3 ≤ n by omega with hn hn
    · -- If n = 2 then 3^3 / 10 = 2 is even.
      simp [hn]
    -- Assume that 3 ≤ n, then Even (3^n / 10).
    -- So we can find k such that 3^n / 10 = 2 * k.
    have ⟨k, hk⟩ := even_iff_exists_two_mul.mp (ih hn)
    -- h3 implies that 3^n % 10 ∈ [1, 3, 7, 9].
    replace h3 := h3 n
    simp at h3
    -- We need to show that
    -- 3^n * 3 / 10 = (10 * (3^n / 10) + 3^n % 10) * 3 / 10
    --    = (10 * (2 * k) * 3 + 3^n % 10 * 3) / 10 is even.
    rw [pow_succ, ← Nat.div_add_mod (3 ^ n) 10, add_mul, hk]
    -- Consider all possible values of 3^n % 10.
    rcases h3 with h3 | h3 | h3 | h3 <;> simp [h3]
    · -- If 3^n % 10 = 1 then (10 * (2 * k) * 3 + 3) / 10 = 2 * (3 * k).
      rw [show (10 * (2 * k) * 3 + 3) / 10 = 2 * (3 * k) by omega]
      exact even_two_mul _
    · -- If 3^n % 10 = 3 then (10 * (2 * k) * 3 + 9) / 10 = 2 * (3 * k).
      rw [show (10 * (2 * k) * 3 + 9) / 10 = 2 * (3 * k) by omega]
      exact even_two_mul _
    · -- If 3^n % 10 = 7 then (10 * (2 * k) * 3 + 21) / 10 = 2 * (3 * k + 1).
      rw [show (10 * (2 * k) * 3 + 21) / 10 = 2 * (3 * k + 1) by omega]
      exact even_two_mul _
    · -- If 3^n % 10 = 9 then (10 * (2 * k) * 3 + 27) / 10 = 2 * (3 * k + 1).
      rw [show (10 * (2 * k) * 3 + 27) / 10 = 2 * (3 * k + 1) by omega]
      exact even_two_mul _