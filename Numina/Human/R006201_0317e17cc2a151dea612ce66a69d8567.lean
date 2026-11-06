import Mathlib

open Finset

/- If there exist $n$ real numbers ${{x}_{1}},{{x}_{2}},\cdots ,{{x}_{n}}$ satisfying ${{x}_{1}}+2{{x}_{2}}+\cdots +n{{x}_{n}}=2009$, and ${{x}_{1}}+{{x}_{2}}+\cdots {{x}_{n}}=0$, where ${{x}_{i}}=\pm 7$, $i=1,2,\cdots ,n$. Try to determine the minimum value of $n$. -/
theorem algebra_9361 : IsLeast {n : ℕ | ∃ x : ℕ → ℝ, ∑ k ∈ range n, (k + 1) * x k = 2009 ∧
    ∑ k ∈ range n, x k = 0 ∧ (∀ i ∈ range n, x i = 7 ∨ x i = -7)} 34 := by
-- Prove an auxillary lemma that $2$ divides $m*(m-1)$ for all natural number $m$
  have aux : ∀ m, 2 ∣ m * (m - 1) := by
    intro m; rcases Nat.even_or_odd' m with ⟨l, hl|hl⟩
    · rw [hl, mul_assoc]; simp
    rw [hl, Nat.add_sub_cancel, mul_comm, mul_assoc]; simp
-- Rewrite the goal to an existential goal and a lower bound goal
  simp [IsLeast, lowerBounds]; constructor
  -- Fulfill the existential goal with a specific sequences $x$ and check it satisfies the desired properties
  · let x : ℕ → ℝ := fun i => if i < 16 then -7 else if i = 17 then -7 else 7
    use x; simp [x]; split_ands
    · simp [sum_range_succ]; norm_num
    · simp [sum_range_succ]
    intro i hi; split_ifs; all_goals norm_num
    all_goals intro; omega
-- Conversely, we need to show that for any sequence satisfying the properties in question, $n$ has to be greater than $34$
  intro n x hx1 hx2 hx3; have npos : 0 < n := by
    by_contra!; simp at this; simp [this] at hx1
-- Denote $P$ to be the index set that $x_i = 7$ and $N$ to be the index set that $x_i = -7$
  let P := {i ∈ range n|x i = 7}; let N := {i ∈ range n|x i = -7}
  have hP : ∀ i ∈ P, x i = 7 := by
    intro i hi; dsimp [P] at hi
    rw [mem_filter] at hi; exact hi.right
  have hN : ∀ i ∈ N, x i = -7 := by
    intro i hi; dsimp [N] at hi
    rw [mem_filter] at hi; exact hi.right
-- Prove that $P$ union $N$ is the whole set $range n$ and $P$, $N$ are disjoint
  have hu : P ∪ N = range n := by
    simp [Finset.ext_iff, P, N]; intro i;
    rw [← and_or_left, iff_comm, iff_self_and]
    exact hx3 i
  have disj : Disjoint P N := by
    simp [P, N, disjoint_iff_inter_eq_empty, Finset.ext_iff]
    intros; linarith
-- Split the summation in `hx1` and `hx2` with repect to $P$ and $Q$
  rw [← hu, sum_union disj] at hx1 hx2
  rw [sum_congr rfl hP, sum_congr rfl hN] at hx2
-- Show that the cardinality of $P$ and $N$ are equal from `hx2` and denote this number to be $k$
  simp at hx2; replace hx2 : (#P : ℝ) = #N := by
    linarith only [hx2]
  norm_cast at hx2; set k := #N with hk
  have hk' : n = 2 * k := by
    apply_fun fun t => #t at hu
    rw [card_union_of_disjoint disj, hx2, ← hk] at hu
    simp at hu; rw [← hu]; ring
-- Let $p$ be the ordering of the index set $P$
  let p : ℕ → ℕ := fun i => Nat.nth (fun j => j ∈ P) i
  have hp : ∀ i < k, x (p i) = 7 := by
    intro i hi; dsimp [p, P]
    have := @Nat.nth_mem (fun j => j ∈ P) i
    specialize this (by intro hf; simp; omega)
    simp [P] at this; simp; exact this.right
  have pinj := @Nat.nth_injOn (fun j => j ∈ P) (by simp)
  simp [hx2] at pinj
-- Prove $p_i$ is less than or equal to $k+i$ by decreasing induction
  have ple : ∀ i < k, p i ≤ k + i := by
    intro i hi; rw [Nat.lt_iff_add_one_le] at hi
    rw [← Nat.le_sub_iff_add_le] at hi
    induction hi using Nat.decreasingInduction with
    | of_succ i h ih =>
      suffices : p i < p (i + 1); omega
      dsimp [p]; apply Nat.nth_lt_nth'; simp
      intro hf; simp; all_goals omega
    | self =>
      dsimp [p]; suffices : Nat.nth (fun j => j ∈ P) (k - 1) < n
      · omega
      have := @Nat.nth_mem (fun j => j ∈ P) (k - 1)
      specialize this (by intro hf; simp; omega)
      simp [P]; simp [P] at this; exact this.left
    omega
  have imgp : image p (range k) = P := by
    have : image p (range k) ⊆ P := by
      simp [Finset.subset_iff, p]; intro i hi
      have := @Nat.nth_mem (fun j => j ∈ P) i
      specialize this (by intro hf; simp; omega)
      exact this
    apply eq_of_subset_of_card_le this
    rw [hx2, card_image_iff.mpr]; simp
    simp [p]; exact pinj
-- Rewrite one of the two summations in `hx1` with respect to the ordering $p$
  have : ∑ i ∈ range k, (p i + 1) * x (p i) = ∑ j ∈ P, (j + 1) * x j := by
    rw [← imgp, sum_image]; intro i; simp [p]
    intro hi j hj hij; apply pinj at hij; exact hij
    all_goals simp; assumption
  rw [← this] at hx1
-- Find an upper bound for this summation
  have Ple : ∑ i ∈ range k, (p i + 1) * x (p i) ≤ ∑ i ∈ range k, ((k:ℝ) + i + 1) * 7 := by
    apply sum_le_sum; intro i hi; simp at hi
    rw [hp]; norm_num; norm_cast
    exact ple i hi; exact hi
  norm_cast at Ple; rw [← sum_mul, sum_add_distrib, sum_add_distrib] at Ple
  simp [sum_range_id] at Ple; rw [Nat.cast_div] at Ple; push_cast at Ple
-- Denote $q$ to be the ordering of the index set $N$
  let q : ℕ → ℕ := fun i => Nat.nth (fun j => j ∈ N) i
  have hq : ∀ i < k, x (q i) = -7 := by
    intro i hi; dsimp [q, N]
    have := @Nat.nth_mem (fun j => j ∈ N) i
    specialize this (by intro hf; simp; omega)
    simp [N] at this; simp; exact this.right
  have qinj := @Nat.nth_injOn (fun j => j ∈ N) (by simp)
  simp [← hk] at qinj
-- Prove that $q_i$ is greater than or equal to $i$ by induction
  have qge : ∀ i < k, i ≤ q i := by
    intro i hi; induction i with
    | zero => simp
    | succ i ih =>
      specialize ih (by omega); suffices : q i < q (i + 1)
      · omega
      dsimp [q]; apply Nat.nth_lt_nth'; simp
      intro hf; simp; all_goals omega
  have imgq : image q (range k) = N := by
    have : image q (range k) ⊆ N := by
      simp [Finset.subset_iff, p]; intro i hi
      have := @Nat.nth_mem (fun j => j ∈ N) i
      specialize this (by intro hf; simp; omega)
      exact this
    apply eq_of_subset_of_card_le this
    rw [← hk, card_image_iff.mpr]; simp
    simp [q]; exact qinj
-- Rewrite the other summation in `hx1` with respect to the ordering $q$
  have : ∑ i ∈ range k, (q i + 1) * x (q i) = ∑ j ∈ N, (j + 1) * x j := by
    rw [← imgq, sum_image]; intro i; simp [q]
    intro hi j hj hij; apply qinj at hij; exact hij
    all_goals simp; assumption
  rw [← this] at hx1
-- Find an upper bound for this summation
  have Nle : ∑ i ∈ range k, (q i + 1) * x (q i) ≤ ∑ i ∈ range k, ((i:ℝ) + 1) * (-7) := by
    apply sum_le_sum; intro i hi; simp at hi
    rw [hq]; norm_num; exact qge i hi; exact hi
  rw [← sum_mul, sum_add_distrib, mul_neg] at Nle; simp at Nle
  rw [← Nat.cast_sum, sum_range_id] at Nle
  rw [Nat.cast_div] at Nle; push_cast at Nle
  rw [Nat.cast_sub] at Ple Nle; push_cast at Nle
-- Put together `hx1`, `Ple` and `Nle`, we can prove that $34$ is a lower bound for $n$
  replace this : (2009 : ℝ) ≤ (k * k + k * (k - 1) / 2 + k) * 7 - ((k * (k - 1) / 2 + k) * 7) := by
    linarith only [Ple, Nle, hx1]
  rw [← sub_nonneg] at this; ring_nf at this
  replace this : 16 ^ 2 < (k : ℝ) ^ 2 := by linarith only [this]
  rw [pow_lt_pow_iff_left₀] at this; norm_cast at this
  any_goals positivity
  any_goals omega
  all_goals apply aux
