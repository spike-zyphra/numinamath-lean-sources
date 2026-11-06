import Mathlib

/-Let  $ f(x) \equal{} c_m x^m \plus{} c_{m\minus{}1} x^{m\minus{}1} \plus{}...\plus{} c_1 x \plus{} c_0$ , where each  $ c_i$  is a non-zero integer. Define a sequence  $ \{ a_n \}$  by  $ a_1 \equal{} 0$  and  $ a_{n\plus{}1} \equal{} f(a_n)$  for all positive integers  $ n$ .

(a) Let  $ i$  and  $ j$  be positive integers with  $ i<j$ . Show that  $ a_{j\plus{}1} \minus{} a_j$  is a multiple of  $ a_{i\plus{}1} \minus{} a_i$ .

(b) Show that  $ a_{2008} \neq 0$ . -/
theorem number_theory_8575 (f : ℤ → ℤ) (c : ℕ → ℤ) (a : ℕ → ℤ) (m : ℕ)
(hf : ∀ t, f t = ∑ i ∈ Finset.range (m + 1), c i * t ^ i)
(hc : ∀ i ∈ Finset.range (m + 1), c i ≠ 0)
(ha : ∀ n, a (n + 1) = f (a n)) (ha0 : a 0 = 0) :
(∀ i k, a (i + 1) - a i ∣ a (i + k + 1) - a (i + k)) ∧ a 2007 ≠ 0 := by
-- Prove a lemma that says for any two values $x$ and $y$, the difference $x-y$ divides the difference $f(x) - f(y)$
  have subd : ∀ x y, x - y ∣ f x - f y := by
    intro x y; simp [hf, ← Finset.sum_sub_distrib]
    apply Finset.dvd_sum; intro i _
    rw [← mul_sub, dvd_mul]; use 1; use x-y; simp
    apply sub_dvd_pow_sub_pow

-- Start proving the first claim by induction on k
  have FC: (∀ i k, a (i + 1) - a i ∣ a (i + k + 1) - a (i + k)) := by
    intro i k; induction k with
    | zero => simp
    | succ n ih =>
      rw [show i+(n+1)+1=i+n+2 by ring, ← add_assoc]
      have h'2 := ha (i+n+1)
      rw [show i+n+1+1=i+n+2 by ring] at h'2
      have h'3 := subd (a (i+n+1)) (a (i+n))
      rw [ha (i+n), ha (i+n+1)]
      exact dvd_trans ih h'3
  constructor; assumption
-- For the second claim, we will prove by contradiction
  intro eq0
-- Prove that the sequence $a_n$ is periodic
  have pda : ∀ k : ℕ, a (k+2007) = a k := by
    intro k; induction k with
    | zero => simp; rw [ha0]; assumption
    | succ k ih =>
      rw [show k+1+2007=k+2008 by ring]
      have r1 := ha k; have r2 := ha (k+2007)
      rw [show k+2007+1=k+2008 by ring] at r2
      rw [r1, r2]; congr
-- In particular, terms whose index are multiples of $2007$ will vanish
  have van : ∀ k, a (2007 * k) = 0 := by
    intro k; induction k with
    | zero => simp; assumption
    | succ n ih =>
      rw [mul_add, mul_one]; rw [pda]; assumption

-- Prove that any $a_n$ has to be a multiple of $c 0$
  have hc0 := hc 0; simp at hc0; push_neg at hc0
  have r1 := FC 0; simp [ha0] at r1
  have r2 := ha 0; simp [ha0, hf] at r2
  simp [← Finset.sum_range_add_sum_Ico (fun x => c x * 0 ^ x) (show 1≤m+1 by simp)] at r2
  have : ∑ i ∈ Finset.Ico 1 (m + 1), c i * 0 ^ i = 0 := by
    apply Finset.sum_eq_zero; simp; intro x _ _; right; linarith
  simp [this] at r2
  have mulc : ∀ k, c 0 ∣ a k := by
    rw [← r2]; intro k; induction k with
    | zero => rw [ha0]; simp
    | succ k ih =>
      have := r1 k; rw [show a (k+1)=a (k+1)-a k + a k by ring]
      apply dvd_add; assumption; assumption

-- Prove that any two adjacent terms $a_k$ and $a_k+1$ differs from each other by $c 0$
  have cdis : ∀ k, (a (k + 1) - a k).natAbs = (c 0).natAbs := by
    intro k; apply Int.natAbs_eq_of_dvd_dvd; by_cases hk : k < 1
    · simp at hk; simp [hk, ha0, r2]
    push_neg at hk
    have := FC k (2006*k); rw [show k+2006*k=2007*k by ring] at this
    simp [van, ha (2007*k)] at this
    rw [← ha0, ← ha 0, r2] at this; assumption
    rw [← r2, ← sub_zero (a 1), ← ha0]
    have := FC 0 k; simp [zero_add] at this; assumption

-- Prove that for any term $a_n$ with odd index, $a_n$ quotient $c 0$ is odd
  have oddq : ∀ k, Odd (a (2*k+1) / c 0) := by
    intro k; induction k with
    | zero => simp [r2, hc0]
    | succ k ih =>
      rw [show 2*(k+1)+1=2*k+3 by ring]
      simp [Int.natAbs_eq_natAbs_iff] at cdis
      have dis1 := cdis (2*k+1); have dis2 := cdis (2*k+2)
      rcases ih with ⟨w, hw⟩; rw [Int.ediv_eq_iff_eq_mul_right] at hw
      simp [hw] at dis1 dis2; cases dis1; rename_i h
      rw [sub_eq_iff_eq_add', show 2*k+1+1=2*k+2 by ring] at h
      nth_rw 2 [← mul_one (c 0)] at h
      rw [← mul_add, show 2*w+1+1=2*w+2 by ring] at h
      cases dis2; rename_i h'
      rw [h, sub_eq_iff_eq_add'] at h'
      nth_rw 2 [← mul_one (c 0)] at h'; rw [← mul_add] at h'
      rw [show 2*k+2+1=2*k+3 by ring, show 2*w+2+1=2*w+3 by ring] at h'
      simp [h', hc0]; use w+1; ring
      rename_i h'
      rw [h, sub_eq_iff_eq_add'] at h'
      nth_rw 2 [← mul_one (c 0)] at h'; rw [← sub_eq_add_neg, ← mul_sub] at h'
      rw [show 2*k+2+1=2*k+3 by ring, show 2*w+2-1=2*w+1 by ring] at h'
      simp [h', hc0]
      rename_i h
      rw [sub_eq_iff_eq_add', show 2*k+1+1=2*k+2 by ring] at h
      nth_rw 2 [← mul_one (c 0)] at h
      rw [← sub_eq_add_neg, ← mul_sub, show 2*w+1-1=2*w by ring] at h
      cases dis2; rename_i h'
      rw [h, sub_eq_iff_eq_add'] at h'
      nth_rw 2 [← mul_one (c 0)] at h'; rw [← mul_add] at h'
      rw [show 2*k+2+1=2*k+3 by ring] at h'
      simp [h', hc0]
      rename_i h'
      rw [h, sub_eq_iff_eq_add'] at h'
      nth_rw 2 [← mul_one (c 0)] at h'; rw [← sub_eq_add_neg, ← mul_sub] at h'
      rw [show 2*k+2+1=2*k+3 by ring] at h'
      simp [h', hc0]; use w-1; ring
      assumption; apply mulc

-- In particular, this means $a_2007/c0$ has to be odd, which is absurd since we assume it to be $0$
  rcases oddq 1003 with ⟨w, hw⟩; simp at hw
  rw [Int.ediv_eq_iff_eq_mul_right, eq0] at hw; simp at hw
  cases hw; contradiction; rename_i h';
  have : Odd (0:ℤ) := by rw [← h']; simp
  contradiction; assumption; simp [eq0]