import Mathlib

open Finset

/-Es sei eine positive ganze Zahl $d$ und eine Folge $\left(a_{i}\right)_{i=1,2,3, \ldots}$ positiver ganzer Zahlen gegeben. Wir nehmen an, dass folgende zwei Bedingungen erfüllt sind:

- Jede positive ganze Zahl taucht genau einmal in der Folge auf.
- Für alle Indizes $i \geq 10^{100}$ gilt $\left|a_{i+1}-a_{i}\right| \leq 2 d$.

Man beweise, dass unendlich viele Indizes $j$ existieren, für die $\left|a_{j}-j\right|< d$ gilt.-/
theorem number_theory_605140 (d : ℕ) (dpos : 0 < d) (a : ℕ → ℤ) (apos : ∀ n, 0 < a n)
(h1 : ∀ m, 0 < m → ∃! n, a n = m) (h2 : ∀ i ≥ 10 ^ 100, |a (i + 1) - a i| ≤ 2 * d) :
{j | |a j - j - 1| < d}.Infinite := by
-- Generalize $10^100$ to any positive integer $l$
  have lpos : 0 < 10 ^ 100 := by simp
  generalize 10^100 = l at lpos h2
-- Assuming the contrary, rewrite and simplify the new assumption
  simp [Set.infinite_iff_exists_gt]; by_contra h; rw [not_forall] at h;
  simp_rw [not_exists, not_and', not_lt, le_abs', sub_le_iff_le_add', ← sub_eq_add_neg] at h
  rcases h with ⟨w, hw⟩; let N := l ⊔ w + 1; have Npos : 0 < N := by simp [N]
  have := Nat.le_max_left l w; have := Nat.le_max_right l w
  have Ngt : l < N ∧ w < N := by simp [N, Nat.lt_add_one_iff]
-- Prove that $a$ is a bijection between $ℕ$ and $Set.Ioi 0$
  have abij : Set.BijOn a Set.univ (Set.Ioi 0) := by
    rw [Set.BijOn]; split_ands; intro i; simp; apply apos
    · intro i; simp; intro j hij; specialize h1 (a i) (apos i)
      rcases h1 with ⟨m,⟨hm,h1⟩⟩; simp at h1; have := h1 i rfl
      have := h1 j (Eq.symm hij); linarith
    · intro y; simp; intro ypos; specialize h1 y ypos
      rcases h1 with ⟨x, ⟨hx⟩⟩; use x
-- According to the reference answer, we can split the goal into the following two cases
-- We will prove the claim by induction
  have key : (∀ i ≥ N, (d : ℤ) + i + 1 ≤ a i) ∨ (∃ M ≥ N, ∀ j ≥ M, a j ≤ j + 1 - d) := by
    by_cases h : ∀ i ≥ N, d + i + 1 ≤ a i; left; exact h
    right; push_neg at h; rcases h with ⟨i, ⟨igt, hi⟩⟩; use i; constructor; exact igt
    intro j; induction j with
    | zero => simp; intro; linarith
    | succ j ihj =>
      intro hij; simp [N] at igt; by_cases h : j < i
      · replace h : j + 1 = i := by linarith
        rw [h]; specialize hw i (show _ by linarith)
        rcases hw with _|h'; all_goals linarith
      specialize ihj (show _ by linarith); specialize h2 j (show _ by linarith)
      rw [abs_le] at h2; specialize hw (j+1) (show _ by linarith); rcases hw with _|h'
      linarith; push_cast at h'; linarith
  rcases key with hA|hB
  -- In case A, we show that $1,2...(N+1)$ is a subset of $a_0, a_1,...a_(N-1)$, which is absurd for cardinality reasons
  · have : (Icc (1:ℤ) (N+1)) ⊆ image a (range N) := by
      simp [subset_iff]; intro i _ hi; by_contra!
      obtain ⟨j, ⟨hj⟩⟩ := h1 i (show _ by linarith); by_cases h' : j < N
      · specialize this j h'; contradiction
      specialize hA j (show _ by linarith)
      replace h' : (N : ℤ) ≤ j := by norm_cast; linarith
      linarith
    apply card_le_card at this; rw [card_image_iff.mpr] at this; simp at this
    intro i; simp; intros; apply abij.injOn; any_goals simp
    assumption
-- In case B, we denote $k$ to be the larger number among $M$ and $a_0, a_1, ... a_(M-1)$
  rcases hB with ⟨M, ⟨Mge, hM⟩⟩; have : (image a (range M)).Nonempty := by
    use a 0; simp; use 0; simp; linarith
  let k := (M : ℤ) ⊔ ((image a (range M)).max' this)
  have Mlek : M ≤ k := by simp [k]
  have alek : ∀ i < M, a i ≤ k := by
    intro i hi; have := le_max' _ (a i) (show a i ∈ (image a (range M)) by simp; use i)
    apply le_trans this; simp [k]
-- Prove that $a_0, a_1, ... a_k$ all falls into the numbers $1, 2, ... k$, which is absurd for cardinality reasons
  have : image a (range (k.natAbs + 1)) ⊆ Icc (1:ℤ) k := by
    simp [subset_iff]; intro i hi; specialize apos i; constructor; linarith
    by_cases h : i < M; apply alek; exact h
    specialize hM i (show _ by linarith); rw [Nat.lt_add_one_iff] at hi; zify at hi
    rw [abs_eq_self.mpr] at hi; all_goals linarith
  apply card_le_card at this; rw [card_image_iff.mpr] at this; zify at this
  simp at this; rw [abs_eq_self.mpr] at this; simp at this; any_goals linarith
  intro i; simp; intros; apply abij.injOn; any_goals simp
  assumption