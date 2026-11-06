import Mathlib

/- # Problem:
 Question 1-1 When any two of the positive divisors of a positive integer $n$ are added together, it is found that these sums are all different, and they are arranged from smallest to largest as $4$, $6$, $8$, $10$, $12$, $14$, $16$, $18$, $20$, $24$, $46$, $48$, $50$, $54$, $60$. from this, determine the value of $n$.
问题 $1-1$ 带有逆向思维的色彩. 从已知条件可得一些有用的信息, 如由 “约数和有 15 个”, 知 $n$ 有六个正约数, 而根据各约数和均为偶数, 知 $n$ 必为奇数, 等等.其实, 为了更直接地确定 $n$ 的值, 可设 $n$ 的最小素因子为 $p$. 则其最小的两个正约数必为 $ 、 p$, 最大的两个正约数必为 $n 、 \frac{n}{p}$. 故 $1+p=4, n+\frac{n}{p}=60$. 进而, $n=45$. -/

def d_list : Finset ℕ := {4, 6, 8, 10, 12, 14, 16, 18, 20, 24, 46, 48, 50, 54, 60}

theorem number_theory_143560 {n : ℕ} (hn : n ≠ 0)
  (h1 : ∀ d1 d2, d1 ∈ n.divisors → d2 ∈ n.divisors → d1 ≠ d2 → d1 + d2 ∈ d_list)
  (h2 : ∀ d, d ∈ d_list → ∃ d1 d2, d1 ∈ n.divisors ∧ d2 ∈ n.divisors ∧ d1 ≠ d2 ∧ d1 + d2 = d)
  (h3 : ∀ d1 d2 d3 d4, d1 ∈ n.divisors → d2 ∈ n.divisors → d3 ∈ n.divisors → d4 ∈ n.divisors
  → d1 + d2 = d3 + d4 → (d1 = d3 ∧ d2 = d4 ∨ d1 = d4 ∧ d2 = d3)) :
    n = 45 := by

  have h1_in : 1 ∈ n.divisors := by
    simp
    exact hn

  have h2_notin : 2 ∉ n.divisors := by
    by_contra h
    have := h1 1 2 h1_in h (by norm_num)
    unfold d_list at this
    simp at this

  have h3_in : 3 ∈ n.divisors := by
    have ⟨d1, d2, hd1, hd2, h12, hsum⟩ := h2 4 (by unfold d_list; simp)
    have : d1 ≤ 4 := by omega
    interval_cases d1
    . simp at hd1
    . have : d2 = 3 := by omega
      subst d2
      exact hd2
    . have : d2 = 2 := by omega
      subst d2
      simp at h12
    . exact hd1
    . have : d2 = 0 := by omega
      subst d2
      simp at hd2

  have h5_in : 5 ∈ n.divisors := by
    have ⟨d1, d2, hd1, hd2, h12, hsum⟩ := h2 6 (by unfold d_list; simp)
    have : d1 ≤ 6 := by omega
    interval_cases d1
    . simp at hd1
    . have : d2 = 5 := by omega
      subst d2
      exact hd2
    . contradiction
    . have : d2 = 3 := by omega
      subst d2
      simp at h12
    . have : d2 = 2 := by omega
      subst d2
      contradiction
    . exact hd1
    . have : d2 = 0 := by omega
      subst d2
      simp at hd2

  have hn_lt_60 : n < 60 := by
    by_contra h
    have := h1 1 n h1_in (by simp; omega) (by omega)
    unfold d_list at this
    simp at this
    omega

  have ⟨k, hk⟩: 15 ∣ n := by
    simp at h3_in
    simp at h5_in
    have := h5_in.1
    have := h3_in.1
    omega

  have : k ≤ 3 := by omega
  interval_cases k
  . omega
  . simp at hk
    subst n
    have ⟨d1, d2, hd1, hd2, h12, hsum⟩ := h2 60 (by unfold d_list; simp)
    simp at hd1 hd2
    have : d1 ≤ 15 := by
      apply Nat.le_of_dvd
      . norm_num
      . exact hd1
    have : d2 ≤ 15 := by
      apply Nat.le_of_dvd
      . norm_num
      . exact hd2
    omega

  . simp at hk
    subst n
    have ⟨d1, d2, hd1, hd2, h12, hsum⟩ := h2 60 (by unfold d_list; simp)
    simp at hd1 hd2
    have : d1 ≤ 30 := by
      apply Nat.le_of_dvd
      . norm_num
      . exact hd1
    have : d2 ≤ 30 := by
      apply Nat.le_of_dvd
      . norm_num
      . exact hd2
    omega
  . rw [hk]
