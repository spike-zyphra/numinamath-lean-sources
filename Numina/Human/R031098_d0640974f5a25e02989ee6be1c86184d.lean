import Mathlib

open Finset

theorem algebra_440955 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (hinc : ∀ n, a n < a (n + 1)) (h1 : a 0 + a 2 = 5) (h2 : a 0 + 3 + (a 2 + 4) = 2 * (3 * a 1)) :
    ∀ n, a n = 2 ^ n ∧ ∑ i ∈ range n, Real.log (a (3 * i + 3)) = 3 * n * (n + 1) / 2 * Real.log 2 := by
  rcases ha with ⟨r, hr⟩
  rw [hr 2] at h1 h2
  rw [← eq_sub_iff_add_eq'] at h1
  rw [h1] at h2; replace h2 : a 1 = 2 := by linarith
  rw [hr 1, pow_one] at h2
  apply_fun fun t => a 0 * t at h1
  rw [show a 0 * (a 0 * r ^ 2) = (a 0 * r) ^ 2 by ring, h2] at h1
  norm_num at h1; rw [← sub_eq_zero] at h1
  simp [show 4 - a 0 * (5 - a 0) = (a 0 - 1) * (a 0 - 4) by ring] at h1
  rcases h1 with h1|h1
  · rw [sub_eq_zero] at h1; simp [h1] at h2
    simp [h1, h2] at hr
    intro n; constructor; exact hr n
    by_cases h : n ≤ 0; simp_all
    simp [hr]; rw [← sum_mul]; congr
    rw [sum_add_distrib, ← mul_sum, ← Nat.cast_sum, sum_range_id]
    rw [Nat.cast_div]; push_cast; rw [Nat.cast_sub]
    push_cast; simp; ring
    omega; obtain ⟨k, hk|hk⟩ := Nat.even_or_odd' n
    · rw [hk, mul_assoc]; simp
    rw [hk, Nat.add_sub_cancel, mul_comm, mul_assoc]; simp
    simp
  specialize hinc 0; simp [hr 1] at hinc; linarith