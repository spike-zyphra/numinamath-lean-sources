import Mathlib

set_option push_neg.use_distrib true

def fib (n : ℕ) : ℕ := match n with
| 0 => 0
| 1 => 1
| n + 2 => fib n + fib (n + 1)

lemma fib_eq {n} : fib n = Nat.fib n := by
  induction' n using fib.induct with n le ih
  · simp [fib]
  · simp [fib]
  · unfold fib
    simp_all [Nat.fib_add_two]


lemma linear_lt_fib {n} (n_gt_5 : 5 < n) : n < fib n := by
  rw [fib_eq]
  induction' n, n_gt_5 using Nat.le_induction with n le ih
  · simp [Nat.fib]
  · have := Nat.fib_lt_fib_succ (by linarith)
    linarith

lemma linear_lt_fib2 {n} (n_gt_5 : 8 < n) : 2*n < fib n := by
  rw [fib_eq]
  induction' n, n_gt_5 using Nat.le_induction with n le ih
  · simp [Nat.fib]
  · have := Nat.fib_lt_fib_succ (by linarith)
    rw [mul_add]
    rw [Nat.fib_add_one]
    suffices 2 < Nat.fib (n - 1) by linarith
    rw [<- fib_eq]
    simp at le
    unfold fib
    split <;> simp_all
      <;> rename_i m m_eq
    · omega
    · suffices 2 < fib m by linarith
      have := linear_lt_fib le
      linarith
    · omega


theorem number_theory_92685 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
  (fib_mul_eq : fib m * fib n = m * n) :
  (m, n) ∈ ({ (1, 1), (1, 5), (4, 6), (5, 1), (5, 5), (6, 4) } : Finset (ℕ × ℕ))
    := by
  wlog n_le_m : n ≤ m
  · suffices (n, m) ∈ ({ (1, 1), (1, 5), (4, 6), (5, 1), (5, 5), (6, 4) } : Finset (ℕ × ℕ)) by
      aesop
    simp at n_le_m
    exact this n m hn hm (by linarith) n_le_m.le

  by_cases le_11 : n < 11 ∧ m < 11
  · have : m < 11 := by linarith
    have : n < 11 := by linarith
    have : (m, n) ∈ (Finset.Ioo 0 11 ×ˢ Finset.Ioo 0 11).filter
        λ (x, y) => fib x * fib y = x * y := by
      simp_all

    exact this
  ·
    push_neg at le_11
    rcases le_11 with (le | le)
    ·
      have n_le_fib := linear_lt_fib (by linarith)
      have m_le_fib := linear_lt_fib (by linarith : 5 < m)
      have : n ≤ fib m := by
        omega
      have : n * m < fib n * fib m := by
        exact Nat.mul_lt_mul'' n_le_fib m_le_fib
      linarith
    ·
      have m_le_fib := linear_lt_fib (by linarith : 5 < m)
      by_cases n_lt : n < 6
      ·
        simp_all
        have := linear_lt_fib2 (by linarith : 8 < m)
        interval_cases n
          <;> simp_all [fib]
          <;> linarith

      simp at n_lt
      by_contra! not_in
      have n_le_fib := linear_lt_fib (by linarith : 5 < n)
      have : m * n < fib m * fib n := by
        exact Nat.mul_lt_mul'' m_le_fib n_le_fib
      linarith
