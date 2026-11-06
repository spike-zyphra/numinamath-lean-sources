import Mathlib

open Finset Real

theorem inequalities_269153 {n : ℕ} (hn : 0 < n) (x : ℕ → ℝ)
    (hx : ∀ i ∈ range n, 0 < x i) :
    ∑ i ∈ range n, (x i)^2 / x ((i + 1) % n) ≥ ∑ i ∈ range n, x i := by

  have am_gm {a b: ℝ} (ha: 0 < a) (hb: 0 < b):
    a^2/b + b ≥ 2*a := by
    have: 2*a = 2 * (a/√b) * √b := by
      have: √b ≠ 0 := sqrt_ne_zero'.mpr hb
      rw [mul_assoc, div_mul_cancel₀ _ this]
    rw [← sq_sqrt (le_of_lt hb), ← div_pow, this]
    apply two_mul_le_add_sq

  have h1: ∑ i ∈ range (n-1), x ((i+1) % n) =
    ∑ i ∈ range (n-1), x (1+i) := by
    refine sum_congr rfl ?_
    intro i; simp only [mem_range]; intro hi
    replace hi: i+1 < n := Nat.add_lt_of_lt_sub hi
    rw [Nat.mod_eq_of_lt hi, add_comm i 1]

  replace h1: ∑ i ∈ range n, x ((i+1) % n) = ∑ i ∈ range n, x i := by
    have: n = n-1+1 := by
      exact (Nat.sub_eq_iff_eq_add hn).mp rfl
    nth_rw 1 [this, sum_range_succ, ← this, Nat.mod_self]
    replace: n = 1 + (n-1) := by
      exact (Nat.add_sub_of_le hn).symm
    nth_rw 3 [this]
    rw [sum_range_add, add_comm _ (x 0), h1, range_one, sum_singleton]

  have h2: ∑ i ∈ range n, x i + ∑ i ∈ range n, x ((i+1) % n) =
    ∑ i ∈ range n, (2 * x i) := by
    rw [h1, ← mul_sum, two_mul]

  have h3: ∑ i ∈ range n, (x i)^2 / x ((i+1) % n) +
    ∑ i ∈ range n, x ((i+1) % n) ≥ ∑ i ∈ range n, (2 * x i) := by
    rw [← sum_add_distrib]
    apply sum_le_sum (fun i hi => ?_)
    apply am_gm (hx i hi) (hx _ ?_)
    simp only [mem_range, Nat.mod_lt (i + 1) hn]

  rwa [← h2, ge_iff_le, add_le_add_iff_right] at h3