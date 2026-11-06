import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat
lemma Nat.add_sub_assoc_of_le {a b c : ℕ } (h : a ≤ a + b - c) : a + b - c = a + (b - c) := by
  have : a + b - b ≤ a + b - c := by simpa
  by_cases hc : c ≤ a + b
  · have := (Nat.sub_le_sub_iff_left hc).1 this
    exact Nat.add_sub_assoc this a
  · push_neg at hc
    have : a = 0 := by rw [Nat.sub_eq_zero_of_le (le_of_lt hc)] at h; linarith
    simp [this]
/-Find all functions $f:\mathbb{N} \to \mathbb{N}$ such that for each natural integer $n>1$ and for all $x,y \in \mathbb{N}$ the following holds: $$ f(x+y) = f(x) + f(y) + \sum_{k=1}^{n-1} \binom{n}{k}x^{n-k}y^k $$-/
theorem number_theory_8841(f : ℕ → ℕ) (n : ℕ) (h : n > 1) (h₀ : ∀ x y, f (x + y) = f x + f y + ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * x ^ (n - k) * y ^ k) :(∃ c, f = fun x => x ^ n + c * x )∨ (f = fun x => x ^ n - x):= by
  --We claim that, $f(x) = (f(1)-1)x + x ^ n$.
  --We use induction to prove that.
  by_cases t : 1 ≤ f 1
  constructor
  use f 1 - 1
  ext x
  induction' x with x ih
  · norm_num
    have g1 : f (0 + 0) = f 0 + f 0 + ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * 0 ^ (n - k) * 0 ^ k := by
      exact h₀ 0 0
    simp at g1
    --When $1 \le f(1)$, we can know that $f(0) = 0$ by using $(0,0)$ to replace $(x,y)$.
    have g2 : ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * 0 ^ (n - k) * 0 ^ k = 0 := by
      simp
      intro x ha hb
      have w1 : x ≠ 0 := by
        exact not_eq_zero_of_lt ha
      have : x ≤ n - 1 := by
        exact hb
      exact Or.inr w1
    rw[g2] at g1
    have : 0 ^ n = 0 := by
      refine Nat.zero_pow ?H
      exact zero_lt_of_lt h
    rw[this]
    simp at g1
    exact g1
  · have h1 : f (1 + x) = f 1 + f x + ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * 1 ^ (n - k) * x ^ k := by
      exact h₀ 1 x
    --By replacing $(x,y)$ with $(1,x)$, we have
    --$$f(x+1) = f(x) + f(1) + \sum_{i=1}^{n-1}\binom{n}{i} x ^ i.$$
    have : 1 + x = x + 1 := by
      exact Nat.add_comm 1 x
    rw[this] at h1
    rw[h1]
    rw[ih]
    symm
    --By induction hypothesis, we only need to prove
    --$$(x + 1) ^ n +(f(1)-1)(x + 1) = x ^ n + (f(1)-1)x +f (1) + \sum_{i=1}^{n-1}\binom{n}{i} x ^ i.$$
    rw[add_pow]
    simp
    rw[mul_add]
    have h2 : ∑ x_1 ∈ Finset.range (n + 1), x ^ x_1 * n.choose x_1 = ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 + 1 + x ^ n := by
      rw [Finset.sum_range_succ, show n = n - 1 + 1 by omega, Finset.sum_range_succ']
      simp
      rw [show Finset.Icc 1 (n - 1) = Finset.Ico 1 n from rfl, Finset.sum_Ico_eq_sum_range]
      apply Finset.sum_congr rfl
      intros
      rw [add_comm]
      ring
    rw[h2]
    have h3 : f 1 + x ^ n + (f 1 - 1) * x = f 1 + (x ^ n + (f 1 - 1) * x) := by
      rw[add_assoc]
    have h4 : f 1 - 1 + 1 = f 1 := by
      rw[add_comm]
      rw[← Nat.add_sub_assoc_of_le]
      simp
      simp
      exact t
    calc
    _ = (f 1 - 1) * 1 + 1 + x ^ n + (f 1 - 1) * x + ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 := by ring
    _ =  f 1 - 1 + 1 + x ^ n + (f 1 - 1) * x + ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 := by simp
    _ = f 1 + x ^ n + (f 1 - 1) * x + ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 := by
      exact Nat.add_right_cancel_iff.mpr (congrFun (congrArg HAdd.hAdd (congrFun (congrArg HAdd.hAdd h4) (x ^ n))) ((f 1 - 1) * x))
    _ = _ := by exact congrFun (congrArg HAdd.hAdd h3) (∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1)
    --That's right by binomial theorem.
  have p : f = fun x => x ^ n - x := by
  --When $1 > f(1)$, since $f(1) \in \N$, $f(1)=0$.
    push_neg at t
    have ha : f 1 = 0 := by exact lt_one_iff.mp t
    ext x
    induction' x with x ih
    · norm_num
      have g1 : f (0 + 0) = f 0 + f 0 + ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * 0 ^ (n - k) * 0 ^ k := by
        exact h₀ 0 0
      simp at g1
      have g2 : ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * 0 ^ (n - k) * 0 ^ k = 0 := by
        simp
        intro x ha hb
        have w1 : x ≠ 0 := by
          exact not_eq_zero_of_lt ha
        have : x ≤ n - 1 := by
          exact hb
        exact Or.inr w1
      rw[g2] at g1
      have : 0 ^ n = 0 := by
        refine Nat.zero_pow ?H
      rw[this]
      simp at g1
      exact g1
    · have h1 : f (1 + x) = f 1 + f x + ∑ k in Finset.Icc 1 (n - 1), Nat.choose n k * 1 ^ (n - k) * x ^ k := by
        exact h₀ 1 x
      have : 1 + x = x + 1 := by
        exact Nat.add_comm 1 x
      rw[this] at h1
      rw[h1]
      rw[ih]
      rw[ha]
      simp
      rw[add_pow]
      simp
      have h2 : ∑ x_1 ∈ Finset.range (n + 1), x ^ x_1 * n.choose x_1 = ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 + 1 + x ^ n := by
        rw [Finset.sum_range_succ, show n = n - 1 + 1 by omega, Finset.sum_range_succ']
        simp
        rw [show Finset.Icc 1 (n - 1) = Finset.Ico 1 n from rfl, Finset.sum_Ico_eq_sum_range]
        apply Finset.sum_congr rfl
        intros
        rw [add_comm]
        ring
      rw[h2]
      symm
      have o : ∃ (m : ℕ) , m = ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 := by
        exact
          exists_apply_eq_apply (fun a => a) (∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1)
      rcases o with ⟨m,hm⟩
      have h3 : ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 + 1 + x ^ n - (x + 1) = x ^ n - x + ∑ x_1 ∈ Finset.Icc 1 (n - 1), n.choose x_1 * x ^ x_1 := by
        rw[← hm]
        rw[add_comm]
        rw[← add_assoc]
        simp
        refine Nat.sub_add_comm ?h
        refine Nat.le_self_pow ?h.hn x
        exact not_eq_zero_of_lt h
      exact h3
  exact Or.inr p
  --It's not hard to prove similarly.
  --Sum up, we know that $f(x) = x ^ n + c * x$ or $f(x) = x ^ n - x$.Here $c$ is a positive integer.
  --Q.E.D.
