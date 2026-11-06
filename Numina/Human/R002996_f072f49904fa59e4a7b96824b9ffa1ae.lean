import Mathlib

/- # Problem:
 $1 \cdot 171$ Let $n \geqslant 5$ and be an integer, divide $n$ into 4 positive integers, i.e., $n=n_{1}+n_{2}$ $+n_{3}+n_{4}$ and $(i, j, p, q)$ are all permutations of $(1,2,3,4)$. Prove: $n$ is a prime number if and only if $n_{i} n_{j} \neq n_{p} n_{q}$.
\[证\] 若 $n$ 不为素数, 则我们可设 $$ n=(a+1)(b+1)=a b+a+b+1 \text {, } $$

这里的 $a$ 和 $b$ 是正整数, 这样给出了符合要求的 $n$ 的一种分法, 但 $a \cdot b$ $=a b \cdot 1$,矛盾.

相反, 设 $n=n_{1}+n_{2}+n_{3}+n_{4}$ 且 $n_{1} n_{2}=n_{3} n_{4}$, 设 $\frac{n_{1}}{n_{4}}=\frac{n_{3}}{n_{2}}=$ $\frac{h}{k}\left(h, k\right.$ 为互质的正整数), 则 $n_{1}=h r, n_{2}=k s, n_{3}=h s, n_{4}=k r$, 于是 $$ n=h r+k s+h s+k r=(h+k)(r+s) $$

这样说明 $n$ 不是素数. -/
theorem number_theory_141300 {n : ℕ} (hn : n ≥ 5):
  Nat.Prime n ↔ ∀ n1 n2 n3 n4, (n = n1 + n2 + n3 + n4 ∧ 0 < n1 ∧ 0 < n2 ∧ 0 < n3 ∧ 0 < n4) → n1 * n2 ≠ n3 * n4 := by

  constructor
  . intro hn_prime
    rintro n1 n2 n3 n4 ⟨hsum, hn1, hn2, hn3, hn4⟩

    by_contra h_contra

    let r := Nat.gcd n1 n4
    let k := n4 / r
    let s := n2 / k
    let h := n1 / r

    have hr : 0 < r := by
      unfold r
      by_contra h_contra
      simp at h_contra
      rw [Nat.gcd_eq_zero_iff] at h_contra
      omega

    have hk : 0 < k := by
      by_contra h_contra
      simp at h_contra
      unfold k at h_contra
      simp at h_contra
      rcases h_contra with h1 | h2
      . omega
      . unfold r at h2
        have := @Nat.gcd_le_right n1 n4 hn4
        omega

    have hh : 0 < h := by
      by_contra h_contra
      simp at h_contra
      unfold h at h_contra
      simp at h_contra
      rcases h_contra with h1 | h2
      . omega
      . unfold r at h2
        have := @Nat.gcd_le_left n1 n4 hn1
        omega

    have hr_dvd_n1 : r ∣ n1 := Nat.gcd_dvd_left n1 n4

    have h1: n1 = h * r := by
      unfold h; symm
      rw [← Nat.dvd_iff_div_mul_eq n1 r]
      exact hr_dvd_n1
    have h4: n4 = k * r := by
      unfold k; symm
      rw [← Nat.dvd_iff_div_mul_eq n4 r]
      exact Nat.gcd_dvd_right n1 n4

    have hk_dvd_n2 : k ∣ n2 := by
      have : n2 * r = n4 * n2.gcd n3 := by
        rw [← Nat.gcd_mul_left n2 n1 n4]
        rw [← Nat.gcd_mul_left n4 n2 n3]
        rw [mul_comm, h_contra]
        rw [Nat.gcd_comm, mul_comm n4 n3]
        rw [mul_comm]

      use n2.gcd n3
      rw [h4] at this
      nlinarith

    have hs : 0 < s := by
      by_contra h_contra
      simp at h_contra
      unfold s at h_contra
      simp at h_contra
      rcases h_contra with h1 | h2
      . omega
      . have := @Nat.le_of_dvd k n2 hn2 hk_dvd_n2
        omega

    have : n = (h + k) * (r + s) := by
      rw [hsum]


      have h2: n2 = k * s := by
        unfold s; symm
        rw [Nat.mul_div_eq_iff_dvd]
        exact hk_dvd_n2

      have h3: n3 = h * s := by
        unfold h s
        rw [Nat.div_mul_div_comm hr_dvd_n1 hk_dvd_n2, h_contra]
        rw [h4, mul_comm r k, Nat.mul_div_left]
        nlinarith
      rw [h1, h4, h2, h3]
      ring

    rw [Nat.prime_def] at hn_prime
    have := hn_prime.2 (h+k) (by use (r+s))
    rcases this with h1 | h2
    . omega
    . rw [h2] at this
      have hrs : r + s = 1 := by nlinarith
      omega

  . intro h
    rw [Nat.prime_def]
    refine ⟨by omega, ?_⟩
    intro u ⟨v, hv⟩
    let a := u - 1
    let b := v - 1

    have ⟨h1_le_u, h1_le_v⟩ : 1 ≤ u ∧ 1 ≤ v := by
      constructor
      all_goals
      . by_contra h_contra
        simp at h_contra
        rw [h_contra] at hv
        omega

    have ha : u = a + 1 := by omega
    have hb : v = b + 1 := by omega

    have : n = a * b + a + b + 1 := by
      rw [hv, ha, hb]
      ring

    by_contra h_contra
    simp at h_contra
    obtain ⟨hu1, hu2⟩ := h_contra

    have ha : a > 0 := by
      omega

    have hb : b > 0 := by
      unfold b
      by_contra h_contra
      simp at h_contra
      have : v = 1 := by omega
      rw [this] at hv
      omega

    have := h (a * b) 1 a b ⟨by omega, by nlinarith, by norm_num, by omega⟩
    contrapose this
    simp
