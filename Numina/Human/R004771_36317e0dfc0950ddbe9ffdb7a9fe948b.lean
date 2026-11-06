import Mathlib

lemma lemma_even_on_z (p : ℤ → Prop)
    (hp : ∀ n : ℕ, p (2 * (n : ℤ))) (hn : ∀ n : ℕ, p (- 2 * (n : ℤ)))
    (x : ℤ) (h : Even x) : p x := by
  obtain ⟨n, h⟩ := h
  have : n + n = 2 * n := by omega
  rw [this] at h
  subst x
  by_cases positivity: n ≥ 0
  . specialize hp n.toNat
    have : n.toNat = n := by omega
    rw [this] at hp
    assumption
  . simp at positivity
    specialize hn ((-n).toNat)
    have : (-n).toNat = -n := by omega
    rw [this] at hn
    simp at hn
    assumption

lemma lemma_odd_on_z (p : ℤ → Prop)
    (hp : ∀ n : ℕ, p (2 * (n : ℤ) + 1)) (hn : ∀ n : ℕ, p (- 2 * (n : ℤ) - 1))
    (x : ℤ) (h : Odd x) : p x := by
  obtain ⟨n, h⟩ := h
  subst x
  by_cases positivity: n ≥ 0
  . specialize hp n.toNat
    have : n.toNat = n := by omega
    rw [this] at hp
    assumption
  . simp at positivity
    specialize hn ((-n).toNat - 1)
    have : ↑((-n).toNat - 1) = -n - 1 := by omega
    rw [this] at hn
    ring_nf at *
    assumption

/- Find all pairs of sets A,B such that A,B satisfy:
(1) A∪B=Z;
(2) If x∈A, then x−1∈B;
(3) If x∈B,y∈B, then x+y∈A.

(2002, Romania for IMO and Balkan Mathematical Olympiad Selection Test (First Round)) -/
theorem number_theory_320449 (A B : Set ℤ) :
    (A ∪ B = Set.univ ∧ (∀ x ∈ A, x-1 ∈ B) ∧ ∀ x ∈ B, ∀ y ∈ B, x+y ∈ A) ↔
    (A = Set.univ ∧ B = Set.univ ∨ A = {x | Even x} ∧ B = {x | Odd x}) := by
  constructor
  . intro ⟨h1, h2, h3⟩
    by_cases h_0 : 0 ∈ B
    . -- By (1) we know $A=\\mathbf{Z}$.
      have a_is_z : A = Set.univ := by
        -- If $0 \\in B$, by (3) we know that for all $x \in B, 0+x \in A$, so, $B \subset A$.
        have b_subset_a : B ⊆ A := by
          specialize h3 0 h_0
          simp at h3
          simp [Set.subset_def]
          assumption
        rw [←h1, Set.union_eq_self_of_subset_right]
        assumption
      -- By (2) we know that for $\\forall x \\in A$, $x-1 \\in B$, so, $B=\\mathbf{Z}$.
      have b_is_z : B = Set.univ := by
        apply Set.ext
        intro x
        constructor
        . simp
        . intro
          have x_plus_one_in_a: x + 1 ∈ A := by
            subst A
            simp
          specialize h2 (x + 1) x_plus_one_in_a
          simp at h2
          assumption
      tauto
    . have x_in_a_or_b (x : ℤ): x ∈ A ∨ x ∈ B := by
        apply Set.mem_or_mem_of_mem_union
        rw [h1]
        simp
      -- If $0 \\notin B$, by (1) we know, $0 \\in A$.
      have zero_in_a : 0 ∈ A := by
        by_contra!
        specialize x_in_a_or_b 0
        tauto
      -- By (2) we know, $-1 \\in B$
      have minus_one_in_b : -1 ∈ B := h2 0 zero_in_a
      -- Therefore, by mathematical induction it is easy to prove that $-2n \\in A, -2n-1 \\in B$ for all non-negative integers $n$.
      have h_below_0 (n : ℕ): -2 * (n : ℤ) ∈ A ∧ -2 * (n : ℤ) -1 ∈ B := by
        induction n with
        | zero => tauto
        | succ n ih =>
            obtain ⟨iha, ihb⟩ := ih
            simp
            ring_nf
            have conclusion_a : -2 - (n : ℤ) * 2 ∈ A := by
              specialize h3 (-2 * n - 1) ihb (-1) minus_one_in_b
              ring_nf at h3
              assumption
            specialize h2 (-2 - n * 2) conclusion_a
            ring_nf at h2
            tauto
      by_cases h_2 : 2 ∈ B
      . -- If $2 \\in B$, then $1=2+(-1) \\in A$, by (2) we know, $1-1=0 \\in B$, which is a contradiction.
        specialize h3 2 h_2 (-1) minus_one_in_b
        specialize h2 1 h3
        contradiction
      -- Therefore, $2 \\notin B, 2 \\in A, 1=2-1 \\in B$.
      have two_in_a : 2 ∈ A := by
        by_contra!
        specialize x_in_a_or_b 2
        tauto
      have one_in_b : 1 ∈ B := h2 2 two_in_a
      -- Next, we prove that for all $n$, $2n \\in A, 2n \\notin B$.
      have h_above_0 (n : ℕ) : 2 * (n : ℤ) ∈ A ∧ 2 * (n : ℤ) ∉ B := by
        revert n
        -- If not, then there exists a smallest $n (n > 1)$ such that $2n \\in B$.
        by_contra!
        obtain ⟨some_n, h⟩ := this
        obtain ⟨n, ⟨⟨two_n_in_b, n_gt_1⟩, minimality⟩⟩ := by
          have hnb : 2 * (some_n : ℤ) ∈ B := by
            by_cases hna : 2 * (some_n : ℤ) ∈ A
            . tauto
            . specialize x_in_a_or_b (2*some_n)
              tauto
          have some_n_gt_one : some_n > 1 := by
            match some_n with
            | 0 => contradiction
            | 1 => contradiction
            | n + 2 => simp
          classical (exact Nat.findX (p := fun n => 2 * (n : ℤ) ∈ B ∧ n > 1) ⟨some_n, by tauto⟩)
        -- Since $-1 \\in B$, we have $2n-1 \\in A$. By (2) we know, $(2n-1)-1=2(n-1) \\in B$
        have h_in_b : 2 * ((n - 1 : ℤ)) ∈ B := by
          specialize h3 (2 * n) two_n_in_b (-1) minus_one_in_b
          specialize h2 (2 * n + (-1)) h3
          ring_nf at *
          assumption
        -- which contradicts the minimality of $n$
        have : ↑(n - 1) = (n : ℤ) - 1 := by omega
        rw [←this] at h_in_b
        have : n - 1 < n := by omega
        simp at minimality
        specialize minimality (n - 1) this h_in_b
        match n with
        | 0 => contradiction
        | 1 => contradiction
        | n + 2 =>
            simp at minimality
            subst n
            contradiction
      -- Thus all positive odd numbers belong to $B$.
      have all_pos_odd_in_b (n : ℕ) : 2 * (n : ℤ) + 1 ∈ B := by
        specialize h_above_0 (n + 1)
        specialize h2 (2 * ↑(n + 1)) h_above_0.left
        have : ↑(n + 1) = (n : ℤ) + 1 := by omega
        rw [this] at h2
        ring_nf at *
        assumption
      -- all even numbers belong to $A$ but not to $B$.
      have even_in_a : ∀ x, Even x → x ∈ A := by
        apply lemma_even_on_z
        . intro n
          specialize h_above_0 n
          tauto
        . intro n
          specialize h_below_0 n
          tauto
      have even_not_in_b : ∀ x, Even x → x ∉ B := by
        apply lemma_even_on_z
        . intro n
          specialize h_above_0 n
          tauto
        . -- If $-2n \\in B$, where $n$ is a positive integer, by $2n+1 \\in B$ and (3) we get $1 \\in A$, and by (2) we get $0 \\in B$, which is a contradiction.
          intro n
          by_contra!
          specialize all_pos_odd_in_b n
          specialize h3 (-2 * n) this (2 * n + 1) all_pos_odd_in_b
          simp at h3
          specialize h2 1 h3
          contradiction
      have odd_in_b : ∀ x, Odd x → x ∈ B := by
        apply lemma_odd_on_z
        . apply all_pos_odd_in_b
        . intro n
          specialize h_below_0 n
          exact h_below_0.right
      have odd_not_in_a : ∀ x, Odd x → x ∉ A := by
        -- If there is an odd number $2n+1 \\in A$, by (2) we get $2n \\in B$, which is a contradiction.
        intro x h
        by_contra!
        specialize h2 x this
        have : Even (x - 1) := by
          rw [Int.even_sub_one, Int.not_even_iff_odd]
          assumption
        specialize even_not_in_b (x - 1) this
        contradiction
      -- Therefore, $A=2\\mathbf{Z}, B=2\\mathbf{Z}+1$.
      have ha : A = {x | Even x} := by
        apply Set.ext
        intro x
        simp
        constructor
        . intros
          by_contra!
          simp at this
          tauto
        . tauto
      have hb : B = {x | Odd x} := by
        apply Set.ext
        intro x
        simp
        constructor
        . intro
          by_contra!
          simp at this
          tauto
        . tauto
      tauto
  . -- the other direction is straightforward
    rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    . substs A B
      simp
    . substs A B
      constructor
      . apply Set.ext
        intro x
        constructor
        . simp
        . simp
          apply Int.even_or_odd
      constructor
      . simp
        intro x h
        apply Even.add_odd
        . assumption
        . apply odd_neg_one
      . simp
        intros
        apply Odd.add_odd <;> assumption
