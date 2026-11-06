import Mathlib
open Finset

/- Let $a_1​,a_2​,a_3​,\dots$ be a non-decreasing sequence of positive integers. For $m \geq 1$, define $b_m ​= \min \{ n : a_n ​\geq m \}$, that is, $b_m$​ is the minimum value of $n$ such that $a_n ​\geq m$. If $a_{19}​=85$, determine the maximum value of $a_1​+a_2​+\dots+a_{19}​+b_1​+b_2​+\dots+b_{85}​. -/
theorem number_theory_96636 :
    IsGreatest {N | ∃ (a : ℕ → ℕ) (ha₀: a 19 = 85) (ha₁: Monotone a),
    ∑ n ∈ Icc 1 19, a n + ∑ m ∈ (Icc 1 85).attach, Nat.find (show ∃ n, 1 ≤ n ∧ a n ≥ m by use 19; simp; linarith [(mem_Icc.mp m.2).2]) = N } 1700 := by
  -- It suffices to show that for every sequence the sum is exactly 1700
  suffices ∀ (a : ℕ → ℕ) (ha₀ : a 19 = 85) (ha₁ : Monotone a), ∑ n ∈ Icc 1 19, a n + ∑ m ∈ (Icc 1 85).attach, Nat.find (show ∃ n, 1 ≤ n ∧ a n ≥ m by use 19; simp; linarith [(mem_Icc.mp m.2).2]) = 1700 by
    constructor
    -- Indeed, to show that 1700 is in the set, we just use the constant sequence $a(n) = 85$
    · simp only [exists_prop, exists_and_left, Set.mem_setOf_eq]
      use fun n => 85; apply And.intro (fun _ _ _ => by simp)
      use by simp
      apply this
      · rfl
      · intros _ _ _; simp
    -- And to show that 1700 is an upper bound, we show that it is even an equality by the assumption
    · intro N
      rw [Set.mem_setOf]
      intro ⟨a, ha₀, ha₁, hN⟩
      rw [this a ha₀ ha₁] at hN
      linarith
  -- To show this, introduce a sequence a satisfying the assumption
  intro a ha₀ ha₁
  let b : _ → ℕ := fun m : (Icc 1 85) => Nat.find (show ∃ n, 1 ≤ n ∧ a n ≥ m by use 19; simp; linarith [(mem_Icc.mp (m.2)).2])
  have hb (x): b x ≤ 20 := by unfold b; simp; use 19; split_ands <;> linarith [(mem_Icc.mp (x.2)).2]
  show ∑ n ∈ Icc 1 19, a n + ∑ m ∈ (Icc 1 85).attach, b m = 1700
  -- Introduce a two dimensional grid, which has a dot at the point
  -- $(m, n)$ iff $m \leq a(n)$. We are only interested in the rectangle
  -- $1 \leq m \leq 85, 1 \leq n \leq 19$
  let grid : ℕ → ℕ → ℕ := fun m n =>
    if m ≤ a n then 1 else 0
  -- For $1 \leq n \leq 19$, the number of dots in the n-th column is exactly $a(n)$
  have h₀ (n : Icc 1 19) : ∑ m ∈ Icc 1 85, grid m n = a n := by
    unfold grid; simp
    have : filter (fun x ↦ x ≤ a ↑n) (Icc 1 85) = Icc 1 (a ↑n) := by
      apply ext; intro x; apply Iff.intro <;> simp
      · omega
      · intros hx₀ hx₁; split_ands <;> try linarith
        · have := ha₁ (show ↑n ≤ 19 by linarith [mem_Icc.mp n.2])
          linarith
    rw [this]
    simp
  -- For $1 \leq m \leq 85$, the number of dots in the m-th row is exactly $b(n)$
  have h₁ (m : Icc 1 85) : ∑ n ∈ Icc 1 19, grid m n = 20 - (b m) := by
    unfold grid; simp
    have : filter (fun x ↦ m ≤ a x) (Icc 1 19) = Icc (b m) 19 := by
      apply ext; intro x; apply Iff.intro <;> unfold b <;> simp
      · intros hx₀ hx₁ hx₂; split_ands; use x; linarith
      · intros x' hx₀ hx₁ hx₂ hx₃; split_ands <;> try linarith
        · linarith [ha₁ hx₀]
    rw [this]; simp
  -- Thus, we can double count the number of dots in the rectangle
  have h₂ := @sum_comm _ _ _ _ (Icc 1 85) (Icc 1 19) grid
  -- We need an auxilary function b' which is defined on all of ℕ to deal with the sums
  let b' := fun m => if hm : m ∈ Icc 1 85 then 20 - b ⟨m, hm⟩ else 0
  have (x) : 20 - b x = b' x := by unfold b'; simp
  -- On one side, it is $\sum_{x=1}^{85} 20 - b(x)$
  have : ∑ x ∈ Icc 1 85, ∑ y ∈ Icc 1 19, grid x y = ∑ (x ∈ (Icc 1 85).attach), (20 - (b x)) := by
    simp_rw [this];
    rw [sum_attach, sum_eq_sum_iff_of_le]
    <;> intro x hx
    <;> rw [h₁ ⟨x, hx⟩]
    <;> unfold b' <;> split <;> simp
  rw [this] at h₂
  -- while on the other side, it is $\sum_{y=1}^{19} a(x)$
  have : ∑ y ∈ Icc 1 19, ∑ x ∈ Icc 1 85, grid x y = ∑ y ∈ Icc 1 19, a y := by
    rw [sum_eq_sum_iff_of_le]
    <;> intro y hy
    on_goal 2 => apply Eq.le
    all_goals exact h₀ ⟨y, hy⟩
  rw [this] at h₂
  -- Rewriting this, we see that the given sum is exactly 1700, as claimed.
  zify [hb] at h₂ ⊢
  rw [sum_sub_distrib] at h₂
  rw [←h₂]; simp