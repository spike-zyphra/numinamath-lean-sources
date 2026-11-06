import Mathlib

/-Compute the unique positive integer $n$ such that
\[2 \cdot 2^2 + 3 \cdot 2^3 + 4 \cdot 2^4 + \dots + n \cdot 2^n = 2^{n + 10}.\]-/
theorem algebra_16021 {n : ℕ} (hn : n > 0) :
    ∑ i ∈ Finset.Icc 2 n, i * 2 ^ i = 2 ^ (n + 10) ↔ n = 513 := by

  have eq (n : ℕ) (hn : n ≥ 2): ∑ i ∈ Finset.Icc 2 n, i * 2 ^ i = (n - 1 : ℝ) * 2 ^ (n + 1) := by
    simp at hn
    have formula :∀m, ∑ i ∈ Finset.range m, i * 2 ^ i = (m - 2 : ℝ) * 2 ^ m + 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Nat.cast_add, ih]
        rw [add_comm, ←add_assoc, add_right_cancel_iff, pow_succ]
        simp
        linarith
    simp
    simp at formula
    have : Finset.Icc 2 n = Finset.range (n + 1) \ Finset.range 2 := by
      ext i
      simp
      omega
    rw [this, Finset.sum_sdiff_eq_sub, formula, formula]
    repeat simp; linarith

  by_cases h: n < 2
  . rw [Finset.Icc_eq_empty_of_lt (by linarith)]
    simp
    constructor
    . intro h₁
      -- 0 = 2^(n+10), which is false
      have : 0 < 2 ^ (n + 10) := by positivity
      linarith
    . intro h₁
      -- when n = 513, it conflicts with h: n < 2
      linarith

  simp at h
  simp at eq
  specialize eq n h

  have cast₁: ∑ i ∈ Finset.Icc 2 n, i * 2 ^ i = ∑ x ∈ Finset.Icc 2 n, (x : ℝ) * 2 ^ x := by
    norm_cast
  have cast₂: (n - 1 : ℝ) * 2 ^ (n + 1) = ((n - 1) * 2 ^ (n + 1) : ℕ) := by
    simp
    rw [Nat.cast_sub (by linarith)]
    norm_cast
  rw [eq, cast₂] at cast₁
  norm_cast at cast₁
  rw [cast₁]
  -- Hence, $(n - 1) 2^{n + 1} = 2^{n + 10},$ so $n - 1 = 2^9 = 512,$ from which $n = \boxed{513}.
  have : (n - 1) * 2 ^ (n + 1) = 2 ^ (n + 10) ↔ (n - 1) = 2 ^ 9 := by
    constructor
    . intro h₁
      rw [(by linarith: (n + 10) = (9 + (n + 1))), pow_add 2 9] at h₁
      rw [mul_right_cancel_iff_of_pos (by positivity)] at h₁
      exact h₁
    . intro h₁
      rw [(by linarith: (n + 10) = (9 + (n + 1))), pow_add 2 9]
      rw [h₁]
  rw [this]
  simp
