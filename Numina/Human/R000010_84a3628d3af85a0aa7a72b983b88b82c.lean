import Mathlib

/-- Auxiliary lemma : $0 + 1 + \cdots + n-1 = \frac {(n-1)*n} 2$. -/
lemma sum_id: ∀ n, (Finset.sum (Finset.range n) fun x => (x : ℝ)) = (↑n - 1) * ↑n / 2 := by
  intro n; symm; apply div_eq_of_eq_mul (by norm_num)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, add_mul, ← ih]
  simp; ring

/-- Given that for any $\( n \in \mathbb{N} \)$, $\( a_{n} > 0 \)$, and
$$
\sum_{j=1}^{n} a_{j}^{3} = \left( \sum_{j=1}^{n} a_{j} \right)^{2}
$$

Prove that $\( a_{n} = n \)$.-/
theorem algebra_4022 (a : ℤ → ℝ) (n : ℕ)(ha0 : a 0 = 0) : ((i : ℕ) → i ≤ n ∧ 1 ≤ i → 0 < a i) →
((i : ℕ) → i ≤ n ∧ 1 ≤ i → (Finset.sum (Finset.range (i + 1)) fun i => a i ^ 3) = (Finset.sum (Finset.range (i + 1)) fun j => a j) ^ 2)
→ ((i : ℕ) → i ≤ n ∧ 1 ≤ i → a i = i) := by
  -- induction on n
  induction' n using Nat.strong_induction_on with n ih
  -- Classify and discuss whether n is greater than 1.
  cases le_or_gt n 1 with
  | inl h => apply Nat.le_one_iff_eq_zero_or_eq_one.mp at h
            -- if $n \leq 1$, there are two cases : $n=0$ or $n=1$.
             cases h with
             | inl h => simp only [h]; simp
             | inr h => simp only [h]; simp; intro t1 t2 i hi1 hi2
                        have t3 : i = 1 := by linarith
                        have t4 : (Finset.sum (Finset.range (1 + 1)) fun i => a ↑i ^ 3) = (Finset.sum (Finset.range (1 + 1)) fun j => a ↑j) ^ 2 := by
                          apply t2 1; linarith; linarith
                        repeat rw [Finset.sum_range_add] at t4
                        repeat rw [Finset.sum_range_one] at t4; simp at t4; repeat rw [ha0] at t4; simp at t4
                        rw [t3]; apply sub_eq_zero.mpr at t4; have : a 1 ^ 3 - a 1 ^ 2 = a 1 ^ 2 *  (a 1 - 1) := by ring
                        rw [this] at t4; simp at t4; cases t4 with
                                                     | inl h' => have t1 : 0 < a 1 := by
                                                                   apply t1 1; linarith; linarith
                                                                 linarith
                                                     | inr h' => simp; linarith
  -- when $1<k$, classify and discuss whether $n$ is greater than $k$.
  | inr h' => intro h1 h2 k ⟨hk1, hk2⟩; apply le_iff_lt_or_eq.mp at hk1; cases hk1 with
              -- if $n$ is greater than $k$, use the induction assume to simplify.
              | inl h => apply ih k; exact h; intro i ⟨hi1, hi2⟩; apply h1 i
                         constructor; linarith; linarith
                         intro j ⟨hj1, hj2⟩; apply h2 j
                         constructor; linarith; linarith
                         constructor; linarith; linarith
              -- the case $k = n$. 
              | inr h => have h2n : (Finset.sum (Finset.range (n + 1)) fun i => a i ^ 3) = (Finset.sum (Finset.range (n + 1)) fun j => a j) ^ 2 := by
                           apply h2 n; constructor; linarith; linarith
                         rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_one, Finset.sum_range_one] at h2n
                         simp at h2n; rw [h]; rw [h] at hk2
                         -- by the inductive hypothesis, we know : $\sum_{j=1}^{k} a_{j}^{3} = \left( \sum_{j=1}^{k} a_{j} \right)^{2}$
                         have h3 : (Finset.sum (Finset.range n) fun x => a ↑x ^ 3) = (Finset.sum (Finset.range n) fun x => a ↑x) ^ 2 := by
                           have : n = n - 1 + 1 := by symm; apply Nat.sub_add_cancel; exact hk2
                           rw [this]; apply h2 (n-1); constructor; linarith; have t1 : 1 < n := by linarith
                           rw [this] at t1; apply Nat.lt_add_one_iff.mp at t1; exact t1
                         have h4 : (Finset.sum (Finset.range n) fun x => a ↑x) = (n - 1) * n / 2 := by
                           have t1 : ∀ x ∈ Finset.range n, a x = x := by
                             intro x hx; simp at hx; cases le_or_lt x 0 with
                             | inr h'x => apply ih x; exact hx;
                                          intro i ⟨hi1, hi2⟩; apply h1 i; constructor; linarith; exact hi2
                                          intro i ⟨hi1, hi2⟩; apply h2 i; constructor; linarith; exact hi2
                                          constructor; linarith; apply Nat.lt_iff_add_one_le.mp at h'x; linarith
                             | inl h'x => apply Nat.le_zero.mp at h'x; rw [h'x]; simp; exact ha0
                           have t2 : (Finset.sum (Finset.range n) fun x => (x : ℝ)) = (↑n - 1) * ↑n / 2 := sum_id n
                           rw [← t2]; apply Finset.sum_congr; rfl; exact t1
                         rw [h3, h4, add_pow_two, add_assoc] at h2n; apply add_left_cancel at h2n
                         apply sub_eq_zero.mpr at h2n
                         -- $a_n ^ 3 - (2 * ((n - 1) * n / 2) * a_n + a_n ^ 2) = a_n * (a_n - n) * (a_n + n - 1)$
                         have : a ↑n ^ 3 - (2 * ((↑n - 1) * ↑n / 2) * a ↑n + a ↑n ^ 2) = a ↑n * (a ↑n - n) * (a ↑n + n - 1) := by ring
                         rw [this] at h2n; simp at h2n; cases h2n with
                           | inl h => cases h with
                             | inl h => have : 0 < a (n : ℤ) := by apply h1 n; constructor; linarith; linarith
                                        linarith
                             | inr h => linarith
                           | inr h => have t1 : a (n : ℤ) = 1 - (n : ℤ) := by
                                        rw [add_sub_assoc] at h; apply add_eq_zero_iff_eq_neg.mp at h; rw [h]; simp
                                      have t2 : 0 < a (n : ℤ) := by apply h1 n; constructor; linarith; linarith
                                      rw [t1] at t2; have t3 : (n : ℝ) < 1 := by linarith
                                      simp at t3; rw [t3] at t1; simp at t1; linarith
