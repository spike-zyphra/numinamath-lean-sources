import Mathlib

open Finset Real

set_option maxHeartbeats 1000000

/-- Let $a_0, a_1, a_2,\cdots$ be a sequence of positive real numbers satisfying $a_{i-1}a_{i+1}\le
a^2_i$ for $i = 1, 2, 3,\cdots$ . (Such a sequence is said to be log concave.) Show that for each
$n > 1$,

\[\frac{a_0+\cdots+a_n}{n+1}\cdot\frac{a_1+\cdots+a_{n-1}}{n-1}\ge\frac{a_0+\cdots+a_{n-1}}{n}
\cdot\frac{a_1+\cdots+a_{n}}{n}.\] -/
theorem inequalities_97089 {a : ℕ → ℝ} (ha : ∀ i, 0 < a i)
    (ha' : ∀ i, a (i - 1) * a (i + 1) ≤ (a i)^2) {n : ℕ} (hn : 1 < n) :
    ((∑ i ∈ Icc 0 n, a i) / (n + 1)) * ((∑ i ∈ Icc 1 (n - 1), a i) / (n - 1)) ≥
    ((∑ i ∈ Icc 0 (n - 1), a i) / n) * ((∑ i ∈ Icc 1 n, a i) / n) := by

  -- For simplicity, let $T(i, j) = \sum_{k=i}^j a_k$ and $P(i, j) = \prod_{k=i}^j a_k$.
  let T (i j : ℕ) := ∑ k ∈ Icc i j, a k
  have hT (i j : ℕ) : T i j = ∑ k ∈ Icc i j, a k := by rfl
  let P (i j : ℕ) := ∏ k ∈ Icc i j, a k
  have hP (i j : ℕ) : P i j = ∏ k ∈ Icc i j, a k := by rfl

  -- We will show that $\frac{T(0, n)}{n+1} \cdot \frac{T(1, n - 1)}{n - 1} \ge \frac{T(0, n - 1)}{n}
  -- \cdot \frac{T(1, n)}{n}$.
  show ((T 0 n) / (n + 1)) * ((T 1 (n - 1)) / (n - 1)) ≥ ((T 0 (n - 1)) / n) * ((T 1 n) / n)

  -- Let's write down a couple of simple inequalities that we will use implicitly in our arguments.
  have : (n : ℝ) ≥ 2 := by norm_cast
  have : (n : ℝ)^2 ≥ 4 := by nlinarith
  have : (n : ℝ) > 0 := by linarith
  have : (n : ℝ) - 1 > 0 := by linarith
  have : (n : ℝ)^2 - 1 > 0 := by nlinarith

  have P_pos (m n : ℕ) (r : ℝ) : 0 < (P m n)^r := by
    apply Real.rpow_pos_of_pos
    simp [P]
    induction' n with n ih
    · by_cases hm : m ≤ 0
      · simp [(by omega : m = 0)]; linarith [ha 0]
      · simp [(by omega : 0 < m)]
    · by_cases hm : ¬ (m ≤ n + 1) <;> simp at hm
      · simp [hm]
      · rw [Finset.prod_Icc_succ_top (by omega)]
        apply mul_pos
        · apply ih
        · linarith [ha (n + 1)]

  have : 0 < a 0 := ha 0
  have : 0 < a n := ha n
  have : 0 < P 0 n := by convert P_pos 0 n 1; simp
  have : 0 < P 1 n := by convert P_pos 1 n 1; simp
  have : 0 < P 0 (n - 1) := by convert P_pos 0 (n - 1) 1; simp
  have : 0 < P 1 (n - 1) := by convert P_pos 1 (n - 1) 1; simp
  have : 0 < (P 0 n)^((1:ℝ) / (n + 1)) := by apply P_pos
  have : 0 < (P 1 (n - 1))^((1:ℝ) / (n - 1)) := by apply P_pos

  have : 0 ≤ (T 1 (n - 1)) / (n - 1) := by
    apply div_nonneg
    apply sum_nonneg
    intros i hi
    · linarith [ha i]
    · simp; linarith
  -------------

  -- Now, because $n^2 - 1 = (n - 1)(n + 1)$, it suffices to show that
  -- $\frac{T(1, n - 1) T(0, n)}{n^2 - 1} \ge \frac{T(0, n - 1) T(1, n)}{n^2}$.
  suffices : ((T 1 (n - 1)) * (T 0 n)) / (n^2 - 1) ≥ ((T 0 (n - 1)) * (T 1 n)) / n^2
  · convert this using 1
    · field_simp; ring
    · ring

  -- We can substract $\frac{T(1, n - 1) T(0, n)}{n^2}$ from both sides.
  suffices (T 1 (n - 1)) * (T 0 n) / (n ^ 2 - 1) - (T 1 (n - 1)) * (T 0 n) / n^2 ≥ (T 0 (n - 1)) * (T 1 n) / n ^ 2 - (T 1 (n - 1)) * (T 0 n) / n^2 by linarith

  -- Notice that, by simple algebra, we have $T(0, (n - 1)) T(1, n) = a_0 a_n + T(1, (n - 1)) T(0, n)$.
  have lem : (T 0 (n - 1)) * (T 1 n) = a 0 * a n + (T 1 (n - 1)) * (T 0 n) := by
    calc _ = (a 0 + (T 1 (n - 1))) * (T 1 n) := by rfl
         _ = (a 0 + (T 1 (n - 1))) * (-(a 0) + (a 0 + (T 1 n))) := by ring
         _ = (a 0 + (T 1 (n - 1))) * (-(a 0) + (T 0 n)) := by rfl
         _ = -(a 0)^2 + (a 0) * ((T 0 n) - (T 1 (n - 1))) + (T 1 (n - 1)) * (T 0 n) := by ring
         _ = -(a 0)^2 + (a 0) * (a 0 + (T 1 n) - (T 1 (n - 1))) + (T 1 (n - 1)) * (T 0 n) := by rfl
         _ = -(a 0)^2 + (a 0) * (a 0 + ((T 1 (n - 1)) + a n) - (T 1 (n - 1))) + (T 1 (n - 1)) * (T 0 n) := by congr; nth_rw 1 [(by omega : n = (n - 1) + 1), hT, sum_Icc_succ_top (by omega), ←hT]; congr; omega
         _ = (a 0) * (a n) + (T 1 (n - 1)) * (T 0 n) := by ring

  -- Substituting this into the inequality, and then simplifying, we are left with the inequality
  -- $\frac{T(1, n - 1) T(0, n)}{(n^2 - 1) n^2} \ge \frac{a_0 a_n}{n^2}$.
  suffices : ((T 1 (n - 1)) * (T 0 n) / (n^2 - 1)) / n^2 ≥ (a 0) * (a n) / n^2
  · convert this using 1
    · field_simp; ring
    · rw [lem]
      field_simp

  -- We can cancel the $n^2$ in the denominator. So, we need to show that
  -- $\frac{T(1, n - 1) T(0, n)}{n^2 - 1} \ge a_0 a_n$.
  gcongr
  show (T 1 (n - 1)) * (T 0 n) / (n ^ 2 - 1) ≥ a 0 * a n

  -- From arithmetic-geometric mean inequality, we have $\frac{T(1, n - 1)}{n - 1} \ge (P(1, n - 1))^{1/(n - 1)}$.
  have : (T 1 (n - 1)) / (n - 1) ≥ (P 1 (n - 1))^((1:ℝ) / (n - 1)) := by
    show (P 1 (n - 1))^((1:ℝ) / (n - 1)) ≤ T 1 (n - 1) / (n - 1)
    convert Real.geom_mean_le_arith_mean (Icc 1 (n - 1)) (fun _ ↦ 1) a (fun _ ↦ (by norm_num)) (by simp [hn]) (fun i hi ↦ by linarith [ha i]) using 2
    · simp [P]
    · simp [Nat.cast_sub (by omega : 1 ≤ n)]
    · simp [T]
    · simp [Nat.cast_sub (by omega : 1 ≤ n)]

  -- We also have $\frac{T(0, n)}{n + 1} \ge (P(0, n))^{1/(n + 1)}$.
  have : (T 0 n) / (n + 1) ≥ (P 0 n)^((1:ℝ) / (n + 1)) := by
    show (P 0 n)^((1:ℝ) / (n + 1)) ≤ (T 0 n) / (n + 1)
    convert Real.geom_mean_le_arith_mean (Icc 0 n) (fun _ ↦ 1) a (fun _ ↦ (by norm_num)) (by simp; linarith) (fun i hi ↦ by linarith [ha i]) using 2
    · simp [P]
    · simp [Nat.cast_sub (by omega : 1 ≤ n)]
    · simp [T]
    · simp [Nat.cast_sub (by omega : 1 ≤ n)]

  -- Then, multiplying these two, we have
  -- $\frac{T(1, n - 1) T(0, n)}{n^2 - 1} \ge (P(1, n - 1))^{1/(n - 1)} (P(0, n))^{1/(n + 1)}$.
  have : ((T 1 (n - 1)) * (T 0 n)) / (n^2 - 1) ≥ (P 1 (n - 1))^((1:ℝ) / (n - 1)) * (P 0 n)^((1:ℝ) / (n + 1)) := by
    calc _ = ((T 1 (n - 1)) / (n - 1)) * ((T 0 n) / (n + 1)) := by ring_nf; field_simp; ring
         _ ≥ _ := by gcongr

  -- Therefore, it suffices to show that
  -- $(P(1, n - 1))^{1/(n - 1)} (P(0, n))^{1/(n + 1)} \ge a_0 a_n$.
  suffices : (P 1 (n - 1))^((1:ℝ) / (n - 1)) * (P 0 n)^((1:ℝ) / (n + 1)) ≥ a 0 * a n
  · calc _ ≥ (P 1 (n - 1))^((1:ℝ) / (n - 1)) * (P 0 n)^((1:ℝ) / (n + 1)) := by assumption
         _ ≥ _ := by assumption

  -- We can raise both sides to the power of $n^2 - 1$.
  suffices : (P 1 (n - 1)^((1:ℝ) / (↑n - 1)) * P 0 n^((1:ℝ) / (↑n + 1)))^(n^2 - (1:ℝ)) ≥ (a 0 * a n)^(n^2 - (1:ℝ))
  · contrapose! this
    gcongr

  -- This way, the powers of $P$ terms become integers.
  suffices : (P 1 (n - 1))^(n + (1:ℝ)) * (P 0 n)^(n - (1:ℝ)) ≥ (a 0)^(n^2 - (1:ℝ)) * (a n)^(n^2 - (1:ℝ))
  · convert this using 1
    · rw [Real.mul_rpow (by linarith) (by linarith), ←Real.rpow_mul (by linarith),
          ←Real.rpow_mul (by linarith)]
      congr
      · field_simp; ring
      · field_simp; ring
    · rw [Real.mul_rpow (by linarith) (by linarith)]

  -- Again by simple algebra, we can transform the inequality into
  -- $P(1, n - 1)^{2n} \ge (a_0 a_n)^{n^2 - n}$.
  have : (P 1 (n - 1))^(n + (1:ℝ)) * (P 0 n)^(n - (1:ℝ)) = (a 0)^(n - (1:ℝ)) * (a n)^(n - (1:ℝ)) * (P 1 (n - 1))^((2:ℝ)*n) := by
    calc _ = (P 1 (n - 1))^(n + (1:ℝ)) * ((a 0) * (P 1 n))^(n - (1:ℝ)) := by rfl
         _ = (P 1 (n - 1))^(n + (1:ℝ)) * ((a 0)^(n - (1:ℝ)) * ((P 1 n))^(n - (1:ℝ))) := by rw [Real.mul_rpow (by linarith) (by linarith)]
         _ = (P 1 (n - 1))^(n + (1:ℝ)) * ((a 0)^(n - (1:ℝ)) * ((P 1 (n - 1)) * (a n))^(n - (1:ℝ))) := by congr; nth_rw 1 [(by omega : n = (n - 1) + 1), hP, prod_Icc_succ_top (by omega), ←hP]; congr; omega
         _ = (P 1 (n - 1))^(n + (1:ℝ)) * ((a 0)^(n - (1:ℝ)) * (((P 1 (n - 1)))^(n - (1:ℝ)) * ((a n))^(n - (1:ℝ)))) := by rw [Real.mul_rpow (by linarith) (by linarith)]
         _ = (a 0)^(n - (1:ℝ)) * ((a n))^(n - (1:ℝ)) * ((P 1 (n - 1))^(n + (1:ℝ)) * ((P 1 (n - 1)))^(n - (1:ℝ))) := by ring
         _ = _ := by rw [←Real.rpow_add (by linarith)]; ring_nf
  rw [this]
  suffices : (P 1 (n - 1))^((2:ℝ)*n) ≥ ((a 0) * (a n))^(n^2 - (n:ℝ))
  · calc _ ≥ (a 0)^(n - (1:ℝ)) * (a n)^(n - (1:ℝ)) * ((a 0) * (a n))^(n^2 - (n:ℝ)) := by gcongr
         _ =  (a 0)^(n - (1:ℝ)) * (a n)^(n - (1:ℝ)) * ((a 0)^(n^2 - (n:ℝ)) * (a n)^(n^2 - (n:ℝ))) := by rw [Real.mul_rpow (by linarith) (by linarith)]
         _ = ((a 0)^(n - (1:ℝ)) * (a 0)^(n^2 - (n:ℝ))) * ((a n)^(n - (1:ℝ)) * (a n)^(n^2 - (n:ℝ))) := by ring_nf
         _ = ((a 0)^(n^2 - (n:ℝ) + n - 1)) * ((a n)^(n - (1:ℝ)) * (a n)^(n^2 - (n:ℝ))) := by rw [←Real.rpow_add (by linarith)]; ring_nf
         _ = ((a 0)^(n^2 - (n:ℝ) + n - 1)) * ((a n)^(n^2 - (n:ℝ) + n - 1)) := by rw [←Real.rpow_add (by linarith)]; ring_nf
         _ = _ := by ring_nf

  -- Now, write $(a_0 a_n)^{n^2 - n} = (a_0)^{n^2 - n} (a_n)^{n^2 - n}$ and take the $n$-th root of
  -- both sides. We are left with the inequality $(P(1, n - 1))^2 \ge (a_0)^{n-1} (a_n)^{n-1}$.
  rw [Real.rpow_mul (by linarith), (by ring : (n^2 - n = (n - (1:ℝ)) * n)),
      Real.rpow_mul (by nlinarith), Real.mul_rpow (by linarith) (by linarith)]
  gcongr

  -- First, observe that $a_i a_n \leq a_{i+1} a_{n-1}$ for any $i < n$. To see this, remember that
  -- by assumption we have $a_i a_{i + 2} \leq (a_{i + 1})^2$,
  -- $a_{i + 1} a_{i + 3} \leq (a_{i + 2}^2$, ..., $a_{n - 2} a_n \leq (a_{n - 1})^2$. Multiplying
  -- all of them and then canceling the same terms, we get the desired inequality.
  have {n i : ℕ} (h : i < n) : a i * a n ≤ a (i + 1) * a (n - 1) := by
    induction' n with n ih generalizing i
    · simp at h
    · rw [Nat.add_one_sub_one]
      by_cases h : n ≤ i <;> simp at h
      · replace h : i = n := by omega
        subst h
        linarith only
      · suffices a i * (a (n - 1) * a (n + 1)) ≤ a (i + 1) * a n * a (n - 1) by nlinarith [ha (n - 1)]
        suffices : (a i) * (a n) * (a n) ≤ a (i + 1) * a (n - 1) * a n
        · calc _ ≤ a i * (a n)^2 := by gcongr; linarith [ha i]; apply ha'
              _ = (a i) * (a n) * (a n) := by ring
              _ ≤ a (i + 1) * a (n - 1) * a n := by assumption
              _ = _ := by ring
        apply mul_le_mul_of_nonneg_right (ih h) (by linarith [ha n])

  -- Repeating this inequality $i$ times starting from $0$, we get $a_0 a_n \leq a_i a_{n - i}$ for
  -- any $i \leq n$.
  have {n i : ℕ} (h : i ≤ n / 2) : a 0 * a n ≤ a i * a (n - i) := by
    induction' i with i ih
    · rfl
    · calc _ ≤ a i * a (n - i) := by apply ih; omega
           _ ≤ a (i + 1) * a (n - i - 1) := by apply this; omega
           _ = _ := by congr 1
  have lem2 {n i : ℕ} (hi : i ≤ n) : a 0 * a n ≤ a i * a (n - i) := by
    by_cases hi' : i ≤ n / 2
    · apply this hi'
    · let j := n - i
      have hj : j ≤ n / 2 := by omega
      convert this hj using 1
      rw [mul_comm]
      congr 2
      simp [j]; omega

  -- Also note that, we have $(a_m a_{m + 1} \dots a_n)^2 = a_m a_{m + 1} \dots
  -- a_n \cdot a_m a_{m + 1} \dots a_n = (a_m a_n) (a_{m + 1} a_{n - 1} \dots (a_n a_m)$
  have (m n : ℕ) (h : m ≤ n) : ∏ i ∈ Icc m n, a i = ∏ i ∈ Icc m n, a (m + n - i) := by
    apply Finset.prod_bij (fun i _ ↦ m + n - i)
    · intro i hi
      simp at hi ⊢
      omega
    · intro i hi j hj h
      simp at hi hj
      omega
    · intro i hi
      simp at hi ⊢
      use m + n - i
      omega
    · intro i hi
      simp at hi
      congr
      omega
  have (m n : ℕ) (h : m ≤ n) : (∏ i ∈ Icc m n, a i)^(2:ℝ) = ∏ i ∈ Icc m n, a i * a (m + n - i) := by
    rw [Finset.prod_mul_distrib, ←this _ _ (by omega), ←Nat.cast_two, Real.rpow_natCast]
    ring

  -- Substituting this into the inequality, we are left with the inequality
  -- $(a_0)^{n - 1} (a_n)^{n - 1} \leq \prod_{i = 1}^{n-1} a_i a_{n - i}$.
  rw [hP, this 1 (n - 1) (by omega), (by omega : 1 + (n - 1) = n)]

  -- Using the inequality $a_0 a_n \leq a_i a_{n-i}$ we just proved, it suffices to show that
  -- $(a_0)^{n - 1} (a_n)^{n - 1} \leq \prod_{i = 1}^{n-1} a_0 a_n = (a_0 a_n)^{n - 1}$ which is
  -- trivially satisfied.
  suffices : (a 0)^(n - (1:ℝ)) * (a n)^(n - (1:ℝ)) ≤ ∏ i ∈ Icc 1 (n - 1), a 0 * a n
  · apply le_trans this
    apply prod_le_prod
    · intro i hi
      nlinarith
    · intro i hi
      simp at hi
      apply lem2
      omega
  apply le_of_eq
  rw [←Real.mul_rpow (by linarith) (by linarith), Finset.prod_const, Nat.card_Icc,
      (by omega : n - 1 + 1 - 1 = n - 1), ←Real.rpow_natCast, Nat.cast_sub (by omega),
      Nat.cast_one]