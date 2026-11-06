import Mathlib

theorem algebra_535046 {a b : ℕ → ℝ} {a1 b1 da db: ℝ}
    (ha: ∀n, a (n+1) = a1 + n * da)
    (hb: ∀n, b (n+1) = b1 + n * db)
    (hSnTn: ∀n, 0 < n →
      (∑ i ∈ Finset.range n, a (i+1)) / (∑ i ∈ Finset.range n, b (i+1)) =
      (2*n+2) / (n+3) ):
    a 10 / b 10 = 20 / 11 := by

  have xsucc {x: ℕ → ℝ} {x1 d:ℝ} {m: ℕ} (hx: ∀m, x (m+1) = x1 + m*d)
    (hm: 0 < m): x (m+1) = x m + d := by
    replace hm: 1 ≤ m := by exact hm
    have: m = m-1 + 1 := by simp [hm]
    nth_rw 2 [this]
    rw [hx m, hx (m-1), Nat.cast_sub hm]
    push_cast
    ring

  have x2n1 {x: ℕ → ℝ} {x1 d:ℝ} {m: ℕ} (hx: ∀m, x (m+1) = x1 + m*d)
    (hm: 0 < m): x (2*m-1+1) = x m + m*d := by
    have h1: 2*m-1 = (2*m-2) + 1 := by omega
    have h2: m = m-1 + 1 := by omega
    nth_rw 2 [h2]
    rw [h1, hx, hx, Nat.cast_sub (by omega)]
    push_cast; rw [Nat.cast_sub (by omega)]
    push_cast; ring

  have x2n2 {x: ℕ → ℝ} {x1 d:ℝ} {m: ℕ} (hx: ∀m, x (m+1) = x1 + m*d)
    (hm: 0 < m): x (2*m-1+1+1) = x m + (m+1)*d := by
    have h1: 2*m-1+1+1 = 2*m+1 := by omega
    have h2: 2*m = 2*m-1+1 := by omega
    rw [h1, xsucc hx (by simp [hm])]
    rw [h2, x2n1 hx hm]
    ring

  have sum_eq_mul_middle {x: ℕ → ℝ} {x1 d: ℝ} (n:ℕ) (hn: 0 < n)
    (hx: ∀m, x (m+1) = x1 + m * d):
    ∑ i ∈ Finset.range (2*n-1), x (i+1) = (2*n-1) * (x n) := by
    have nge1: n ≥ 1 := by exact hn
    induction' n,nge1 using Nat.le_induction with n nge ih
    · norm_num
    · have npos: 0 < n := by exact nge
      have h1: 2*(n+1)-1 = (2*n-1) + 1 + 1 := by omega
      have h2: ∑ i ∈ Finset.range (2*(n+1)-1), x (i+1) =
        ∑ i ∈ Finset.range (2*n-1), x (i+1) + x (2*n-1+1) + x (2*n-1+1+1) := by
        rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
      rw [h2, ih npos, xsucc hx npos, x2n1 hx npos, x2n2 hx npos]
      push_cast
      ring

  have: a 10 / b 10 = ( ∑ i ∈ Finset.range (2*10-1), a (i+1) )
    / ∑ i ∈ Finset.range (2*10-1), b (i+1) := by
    rw [sum_eq_mul_middle 10 (by norm_num) ha,
    sum_eq_mul_middle 10 (by norm_num) hb]
    ring

  rw [this, hSnTn _ (by norm_num)]
  norm_num