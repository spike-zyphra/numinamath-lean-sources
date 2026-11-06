import Mathlib

set_option maxHeartbeats 600000

-- Let $p$ be a prime number and $N$ be a positive integer. For any natural number $n$ (where $1 \le n \le N$), connect the origin $O(0,0)$ with the point $A_{n}(n, n+p)$. Let $f(n)$ denote the number of integer points on the line segment $O A_{n}$ strictly between $O$ and $A_n$. Determine the value of the sum $S = \sum_{i=1}^N f(i)$. Show that the answer is $(p-1)\lfloor N/p \rfloor$.
theorem number_theory_636233 {p : ℕ} (hp : Nat.Prime p) {N : ℕ} (hN : 0 < N) :
    let f n := {⟨x, y⟩ : ℤ × ℤ | x > 0 ∧ x < n ∧ x * (n + p) = y * n}.ncard
    ∑ i in Finset.Icc 1 N, f i = (p - 1) * (N / p) := by
  intro f
  /-
  1. The number of integer points $f(n)$ on the line segment $OA_n$ strictly between $O(0,0)$ and $A_n(n, n+p)$ is given by $f(n) = \gcd(n, n+p) - 1$.\
    Let $g = \gcd(n, n+p)$. The integer points on the segment $OA_n$ are $(k \cdot n/g, k \cdot (n+p)/g)$ for $k=0, 1, \dots, g$. There are $g+1$ such points. The points $O$ and $A_n$ correspond to $k=0$ and $k=g$. The points strictly between $O$ and $A_n$ correspond to $k=1, \dots, g-1$. Thus, there are $g-1$ such points, so $f(n)=g-1$.
  -/
  have : ∀ n : ℕ, n > 0 → f n = n.gcd (n + p) - 1 := by
    intro n n_pos
    unfold f
    set g := n.gcd (n + p)
    have g_pos : g > 0 := by
      unfold g
      exact Nat.gcd_pos_of_pos_left (n + p) n_pos
    have : n / g > 0 := by
      exact Nat.div_gcd_pos_of_pos_left (n + p) n_pos
    have : g ∣ n := by
      exact Nat.gcd_dvd_left n (n + p)
    rcases this with ⟨a, n_eq_g_a⟩
    have a_pos : a > 0 := by
      nlinarith
    have : g ∣ n + p := by
      exact Nat.gcd_dvd_right n (n + p)
    rcases this with ⟨b, n_add_p_eq_g_b⟩
    have b_pos : b > 0 := by
      nlinarith
    let s : Finset (ℤ × ℤ) := (Finset.Ioo 0 g).map ⟨
      fun (k : ℕ) => ⟨k * a, k * b⟩,
      by
        simp [Function.Injective]
        have a_ne_0 : a ≠ 0 := by
          linarith
        simp [a_ne_0]
    ⟩
    have : {⟨x, y⟩ : ℤ × ℤ | x > 0 ∧ x < n ∧ x * (n + p) = y * n} =
        s := by
      unfold s
      ext ⟨x, y⟩
      simp
      constructor
      . /-
        simp
        rintro x_gt_0 x_lt_n x_mul_n_plus_p_eq_y_mul_n
         -/
        rintro ⟨x_gt_0, x_lt_n, x_mul_n_plus_p_eq_y_mul_n⟩
        have : x.toNat > 0 := by
          omega
        have x_eq_toNat : x = x.toNat := by
          omega
        have : y > 0 := by
          nlinarith
        have y_eq_toNat : y = y.toNat := by
          omega
        rw [x_eq_toNat, y_eq_toNat] at x_mul_n_plus_p_eq_y_mul_n
        norm_cast at x_mul_n_plus_p_eq_y_mul_n
        rw [n_add_p_eq_g_b, n_eq_g_a] at x_mul_n_plus_p_eq_y_mul_n
        have x_b_eq_y_a : x.toNat * b = y.toNat * a := by
          nlinarith
        -- This could possibly be moved outside.
        have a_coprime_b : a.Coprime b := by
          have gcd_eq_g : n.gcd (n + p) = g := rfl
          rw [n_add_p_eq_g_b, n_eq_g_a] at gcd_eq_g
          have : (g * a).gcd (g * b) = g * a.gcd b := by
            exact Nat.gcd_mul_left g a b
          rw [this] at gcd_eq_g
          nlinarith
        have : a ∣ x.toNat := by
          have : a ∣ x.toNat * b := by
            exact Dvd.intro_left y.toNat x_b_eq_y_a.symm
          exact Nat.Coprime.dvd_of_dvd_mul_right a_coprime_b this
        rcases this with ⟨k, x_toNat_eq_a_k⟩
        use k
        constructor
        . constructor
          . nlinarith
          . have : x.toNat < n := by
              linarith
            rw [x_toNat_eq_a_k, n_eq_g_a] at this
            nlinarith
        . rw [x_eq_toNat, y_eq_toNat]
          norm_cast
          constructor
          . rw [x_toNat_eq_a_k]
            ring
          . nlinarith
      . rintro ⟨k, ⟨k_gt_0, k_lt_g⟩, rfl, rfl⟩
        norm_cast
        constructor
        . nlinarith
        constructor
        . nlinarith
        . rw [n_add_p_eq_g_b, n_eq_g_a]
          ring
    rw [this]
    norm_cast
    simp [s]
  rw [
    Finset.sum_congr rfl (
      fun i i_in_icc =>
        this i (by
          simp at i_in_icc
          linarith
        )
    )
  ]
  /-
  2. Simplify $\gcd(n, n+p)$. Using the property $\gcd(a,b) = \gcd(a, b-a)$, we get $\gcd(n, n+p) = \gcd(n, (n+p)-n) = \gcd(n,p)$.\
    So, $f(n) = \gcd(n,p) - 1$.
  -/
  simp
  /-
  3. Evaluate $f(n)$ using the fact that $p$ is a prime number.

    - If $n$ is not a multiple of $p$, then $\gcd(n,p)=1$ (since $n \ge 1$). In this case, $f(n) = 1-1 = 0$.
    - If $n$ is a multiple of $p$, then $\gcd(n,p)=p$. In this case, $f(n) = p-1$.

  4. Compute the sum $S = \sum_{n=1}^N f(n)$.\
    The terms $f(n)$ are non-zero only when $n$ is a multiple of $p$.\
    $S = \sum_{\substack{n=1 \\ p \mid n}}^N (p-1)$.\
    The values of $n$ in the sum are $p, 2p, 3p, \ldots, kp$, where $kp \le N$.\
    The largest such $k$ is $\lfloor N/p \rfloor$.\
    The number of such values of $n$ is $\lfloor N/p \rfloor$.\
    Each such term in the sum contributes $p-1$.\
    So, $S = (p-1) \cdot (\text{number of multiples of } p \text{ in } [1,N])$.\
    $S = (p-1) \lfloor N/p \rfloor$.
  -/
  let s := (Finset.Icc 1 N).filter (p ∣ .)
  let t := (Finset.Icc 1 N).filter (¬ p ∣ .)
  have eq_union : Finset.Icc 1 N = s ∪ t := by
    unfold s t
    exact Eq.symm (Finset.filter_union_filter_neg_eq (fun x ↦ p ∣ x) (Finset.Icc 1 N))
  rw [eq_union]
  have disjoint : Disjoint s t := by
    unfold s t
    exact Finset.disjoint_filter_filter_neg (Finset.Icc 1 N) (Finset.Icc 1 N) fun x ↦ p ∣ x
  rw [Finset.sum_union disjoint]
  have : ∑ i ∈ t, (i.gcd p - 1) = 0 := by
    simp
    unfold t
    simp
    intro i _ _ not_p_dvd_i
    have : i.gcd p = 1 := by
      show i.Coprime p
      suffices p.Coprime i by
        exact Nat.coprime_comm.mp this
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr not_p_dvd_i
    simp [this]
  simp [this]

  have : ∀ i ∈ s, i.gcd p - 1 = p - 1 := by
    simp [s]
    intro i _ _ p_dvd_i
    have : i.gcd p = p := by
      exact Nat.gcd_eq_right p_dvd_i
    rw [this]
  rw [Finset.sum_congr rfl this]
  rw [Finset.sum_const]
  simp
  have : s.card = N / p := by
    --simp [s]
    have : s = (Finset.Ioc 0 (N / p)).map ⟨(. * p), by
      have : p ≠ 0 := by
        exact hp.ne_zero
      simp [Function.Injective, this]
    ⟩ := by
      ext n
      simp [s]
      have p_pos := hp.pos
      constructor
      . simp
        intro n_gt_0 n_le_N p_dvd_n
        rcases p_dvd_n with ⟨k, n_eq_k_p⟩
        use k
        constructor
        . constructor
          . nlinarith
          . suffices k * p ≤ N by
              exact (Nat.le_div_iff_mul_le p_pos).mpr this
            linarith
        . linarith
      . simp
        intro k k_pos k_le_N k_p_eq_n
        constructor
        . constructor
          . nlinarith
          . have : n ≤ (N / p) * p := by
              --rw [←k_p_eq_n]
              nlinarith
            have : (N / p) * p ≤ N := by
              exact Nat.div_mul_le_self N p
            linarith
        . exact Dvd.intro_left k k_p_eq_n
    rw [this]
    simp
  rw [this]
  ring
  -- This completes the derivation.
