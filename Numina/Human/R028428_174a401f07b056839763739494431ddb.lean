import Mathlib

open Finset Real

/- Soit $n \geqslant 3$ un nombre entier et $a_{1}, a_{2}, \ldots, a_{n}$ des nombres réels.
(a) On suppose que $a_{i}<\max \left(a_{i-1}, a_{i+1}\right)$ pour tout $i \in\{2,3, \ldots, n-1\}$. Montrer que $a_{i}<$ $\max \left(a_{1}, a_{n}\right)$ pour tout $i \in\{2,3, \ldots, n-1\}$.
(b) On suppose que $a_{i} \leqslant \max \left(a_{i-1}, a_{i+1}\right)$ pour tout $i \in\{2,3, \ldots, n-1\}$. Est-il vrai que $a_{i} \leqslant \max \left(a_{1}, a_{n}\right)$ pour tout $i \in\{2,3, \ldots, n-1\}$ ?
N.B. Si $x$ et y sont deux nombres réels, on note $\max (x, y)$ le plus grand des deux. -/
theorem inequalities_607622 {n : ℕ} (hn : 3 ≤ n) (a : ℕ → ℝ)
    (h : ∀ i ∈ Icc 2 (n - 1), a i < max (a (i - 1)) (a (i + 1))) :
    ∀ i ∈ Icc 2 (n - 1), a i < max (a 1) (a n) := by
  let F : Finset ℝ := (a '' (Icc 1 n)).toFinset
  have Fnon : F.Nonempty := by
    use a 1
    simp only [F, Set.toFinset_image, mem_image]
    use 1
    refine ⟨?_, rfl⟩
    simp only [coe_Icc, Set.toFinset_Icc]
    exact mem_Icc.mpr ⟨le_rfl, Nat.one_le_of_lt hn⟩
  -- Let r be the maximal element of the sequence, and let i be an index such that a_i = r.
  obtain ⟨r, hr⟩ := F.max_of_nonempty Fnon
  have rMem := F.mem_of_max hr
  simp only [F, Set.toFinset_image, mem_image] at rMem
  obtain ⟨i, ⟨hi, har⟩⟩ := rMem
  simp only [coe_Icc, Set.toFinset_Icc, mem_Icc] at hi
  -- Any element of the sequence not in the edges is strictly smaller than the maximum, because it's
  -- smaller than one of its neighbors, which is smaller of equal to the maximum.
  have hmax : ∀ j ∈ Icc 2 (n - 1), a j < a i := by
    have hm : ∀ j ∈ Icc 1 n, a j ≤ a i := by
      intro j hj
      have := F.le_max (show a j ∈ F by
        have := trivial
        simp only [F, Set.toFinset_image, coe_Icc, Set.toFinset_Icc, mem_image]
        use j)
      simp_all only [WithBot.coe_le_coe]
    intro j hj
    apply (h j hj).trans_le
    rw [mem_Icc] at hj
    have aux1 : j - 1 ∈ Icc 1 n := by
      rw [mem_Icc]
      constructor
      · exact Nat.le_sub_one_of_lt hj.1
      · exact ((Nat.sub_le j 1).trans hj.2).trans (Nat.sub_le n 1)
    have aux2 : j + 1 ∈ Icc 1 n := by
      rw [mem_Icc]
      constructor
      · exact ((NeZero.one_le : 1 ≤ 2).trans hj.1).trans (Nat.le_succ j)
      · have := add_le_add_right hj.2 1
        rwa [Nat.sub_add_cancel (Nat.one_le_of_lt hn : 1 ≤ n)] at this
    exact max_le (hm (j - 1) aux1) (hm (j + 1) aux2)
  -- Therefore it is enough to show the the maximum is attained at one of the 2 ends of the array,
  -- since every element not in the edges is strictly less than the maximum.
  suffices hr : i = 1 ∨ i = n by
    intro j hj
    have := hmax j hj
    apply this.trans_le
    cases' hr with hr hr
    · rw [hr]
      exact le_max_left _ _
    · rw [hr]
      exact le_max_right _ _
  -- If the maximum is not at the first or last index, then it is strictly smaller than one of its
  -- neighbors, a contradiction.
  by_contra! h
  have : i ∈ Icc 2 (n - 1) := by
    rw [mem_Icc]
    constructor
    · exact hi.1.eq_or_gt.resolve_left h.1
    · exact Nat.le_sub_one_of_lt <| hi.2.eq_or_lt.resolve_left h.2
  exact lt_irrefl _ (hmax i this)
