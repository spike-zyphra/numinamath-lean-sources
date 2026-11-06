import Mathlib

open Finset Real Nat

set_option maxHeartbeats 300000

/-Let S be a subset of the set {1,2,3,…,2015} such that for any two elements a,b∈S, the difference a−b does not divide the sum a+b.
Find the maximum possible size of S.-/

theorem Number_Theory_609435: IsGreatest {k: ℕ | ∃ S: Finset ℕ, (S ⊆  Icc 1 2015) ∧ (∀ a b: ℕ, (a ∈ S) ∧ (b ∈ S) ∧ (a > b) → ¬ (a - b) ∣ (a + b)) ∧ (k = S.card)} 672 := by
  -- max_subset_size is the most hard part of the problem --
  have max_subset_size : ∀ (A : Finset ℕ), (A ⊆ Finset.Icc 1 2015 ∧
  ∀ (a b : ℕ), (a ∈ A) ∧ (b ∈ A) ∧ (a > b) →  ¬ (a - b) ∣ (a + b)) → A.card ≤ 672 := by
    intro A
    simp
    intro hA
    intro H
    -- construct the "desks: {1,2,3},{4,5,6}..." --
    -- to insure the injectivity of the map f, we need to modify on the definition --
    let f (k : ℕ) : Finset ℕ :=
    if k ≤ 671 then
      Finset.Icc (3 * k + 1) (min (3 * k + 3) 2015)
    else
      Finset.Icc (3 * k + 1) (3 * k + 3)
    -- we need to verify the injectivity of f --
    have hf: Function.Injective f := by
      intro k1 k2 eq
      simp [f] at eq
      by_cases c: k1 ≤ 671
      . have d: k2 ≤ 671 := by
          by_contra! d
          have d1: ¬ k2 ≤ 671 := by omega
          simp [c,d1] at eq
          have hk2: (3 * k1 + 1) ∈ Finset.Icc (3 * k1 + 1) ((3 * k1 + 3) ⊓ 2015) := by simp; omega
          rw [eq] at hk2
          simp at hk2
          have hk1: (3 * k2 + 1) ∈ Finset.Icc (3 * k2 + 1) (3 * k2 + 3) := by simp
          rw [← eq] at hk1
          simp at hk1
          omega
        simp [c,d] at eq
        have hk2: (3 * k1 + 1) ∈ Finset.Icc (3 * k1 + 1) ((3 * k1 + 3) ⊓ 2015) := by simp; omega
        rw [eq] at hk2
        simp at hk2
        have hk1: (3 * k2 + 1) ∈ Finset.Icc (3 * k2 + 1) ((3 * k2 + 3) ⊓ 2015) := by simp; omega
        rw [← eq] at hk1
        simp at hk1
        omega
      . have d: ¬ k2 ≤ 671 := by
          by_contra! d
          simp [c,d] at eq
          have hk2: (3 * k1 + 1) ∈ Finset.Icc (3 * k1 + 1) (3 * k1 + 3):= by simp
          rw [eq] at hk2
          simp at hk2
          have hk1: (3 * k2 + 1) ∈ Finset.Icc (3 * k2 + 1) ((3 * k2 + 3) ⊓ 2015) := by simp;omega
          rw [← eq] at hk1
          simp at hk1
          omega
        simp [c,d] at eq
        have hk2: (3 * k1 + 1) ∈ Finset.Icc (3 * k1 + 1) (3 * k1 + 3) := by simp
        rw [eq] at hk2
        simp at hk2
        have hk1: (3 * k2 + 1) ∈ Finset.Icc (3 * k2 + 1) (3 * k2 + 3) := by simp
        rw [← eq] at hk1
        simp at hk1
        omega
    let g: ℕ ↪ Finset ℕ := ⟨f,hf⟩
    let blocks : Finset (Finset ℕ) :=
      (Finset.range 672).map g
    -- Block.card = 672 --
    have blockcard: blocks.card = 672 := by
      simp [blocks, Finset.card_map, Finset.card_range]
    -- Each block has size at most 3
    have h_block_size : ∀ (B : Finset ℕ), B ∈ blocks → B.card ≤ 3 := by
      intro B hB
      simp [blocks, Finset.mem_map] at hB
      obtain ⟨k,hk⟩:= hB
      rcases hk with ⟨i,j⟩
      replace j: B = Finset.Icc (3 * k + 1) (min (3 * k + 3) 2015) := by
        rw [← j]
        simp [g,f]
        intro o
        omega
      simp [j]
      omega
    -- A intersects each block in at most 1 element --
    have h_block_intersection : ∀ (B : Finset ℕ), B ∈ blocks → (A ∩ B).card ≤ 1 := by
      intro B hB
      by_contra h
      push_neg at h
      have h_gt : (A ∩ B).card ≥ 2 := by linarith
      simp [blocks] at hB
      obtain ⟨k,hk⟩:= hB
      rcases hk with ⟨i,j⟩
      replace j: B = Finset.Icc (3 * k + 1) (min (3 * k + 3) 2015) := by
        rw [← j]
        simp [g,f]
        intro o
        omega
      by_cases hk2: k = 671
      . rw [hk2] at j
        simp at j
        have AB: A ∩ B = B := by
          have SizeB: B.card = 2 := by
            rw [j]
            simp
          replace h_gt: (A ∩ B).card ≥ B.card := by rw [SizeB]; exact h_gt
          have sub: A ∩ B ⊆ B := by simp
          apply Finset.eq_of_subset_of_card_le sub h_gt
        have subset: B ⊆ A := by rw [← AB]; simp
        have elem1: 2014 ∈ A := by
          rw [j] at subset
          have o1: 2014 ∈ Finset.Icc 2014 2015 := by simp
          apply Set.mem_of_mem_of_subset o1 subset
        have elem2: 2015 ∈ A := by
          rw [j] at subset
          have o2: 2015 ∈ Finset.Icc 2014 2015 := by simp
          apply Set.mem_of_mem_of_subset o2 subset
        specialize H 2015 2014
        simp at H
        simp [elem2] at H
        absurd H
        exact elem1
      . replace j: B = Finset.Icc (3 * k + 1) ((3 * k + 3)) := by
          have eq: (3 * k + 3) ⊓ 2015 = 3 * k + 3 := by omega
          rw [eq] at j
          exact j
        by_cases AB: (A ∩ B).card = 2
        . rw [Finset.card_eq_two] at AB
          obtain ⟨a,b,l⟩:= AB
          rcases l with ⟨ne,elem⟩
          by_cases ineq2: a > b
          . specialize H a b
            have ha: a ∈ B := by
              have ha1: a ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ B := by simp
              apply Set.mem_of_mem_of_subset ha1 u
            have aA: a ∈ A := by
              have ha1: a ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ A := by simp
              apply Set.mem_of_mem_of_subset ha1 u
            have hb: b ∈ B := by
              have hb1: b ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ B := by simp
              apply Set.mem_of_mem_of_subset hb1 u
            have bA: b ∈ A := by
              have hb1: b ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ A := by simp
              apply Set.mem_of_mem_of_subset hb1 u
            simp [j] at ha hb
            have ineq: a - b ≤ 2 := by omega
            have case: (a - b = 1) ∨ (a - b = 2) := by omega
            rcases case with p | q
            . have contra: a - b ∣ a + b := by rw [p]; omega
              simp [aA,bA,ineq2] at H
              absurd H
              exact contra
            . have dvd2: 2 ∣ a + b := by
                rw [show a + b = a - b + 2 * b by omega]
                rw [q]
                simp
              simp [aA,bA,ineq2,q] at H
              omega
          . replace ineq2: a < b := by omega
            specialize H b a
            have ha: a ∈ B := by
              have ha1: a ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ B := by simp
              apply Set.mem_of_mem_of_subset ha1 u
            have aA: a ∈ A := by
              have ha1: a ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ A := by simp
              apply Set.mem_of_mem_of_subset ha1 u
            have hb: b ∈ B := by
              have hb1: b ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ B := by simp
              apply Set.mem_of_mem_of_subset hb1 u
            have bA: b ∈ A := by
              have hb1: b ∈ A ∩ B := by simp [elem]
              have u: A ∩ B ⊆ A := by simp
              apply Set.mem_of_mem_of_subset hb1 u
            simp [j] at ha hb
            have ineq: b - a ≤ 2 := by omega
            have case: (b - a = 1) ∨ (b - a = 2) := by omega
            rcases case with p | q
            . have contra: b - a ∣ b + a := by rw [p]; omega
              simp [aA,bA,ineq2] at H
              omega
            . have dvd2: 2 ∣ a + b := by
                rw [show a + b = b - a + 2 * a by omega]
                rw [q]
                simp
              simp [aA,bA,ineq2,q] at H
              omega
        . have ABSize: (A ∩ B).card ≤ 3 := by
            calc
              (A ∩ B).card ≤ B.card := by apply Finset.card_le_card; simp
                        _ = 3 := by rw [j]; simp
          replace ABSize: (A ∩ B).card = 3 := by omega
          have Bcard: B.card = 3 := by rw [j]; simp
          rw [← Bcard] at ABSize
          replace AB: (A ∩ B) = B := by apply Finset.eq_of_subset_of_card_le; simp; omega
          replace AB: B ⊆ A := by rw [← AB]; simp
          rw [j] at AB
          have o1: 3 * k + 1 ∈ Finset.Icc (3 * k + 1) (3 * k + 3) := by simp
          replace o1: 3 * k + 1 ∈ A := by apply Set.mem_of_mem_of_subset o1 AB
          have o2: 3 * k + 2 ∈ Finset.Icc (3 * k + 1) (3 * k + 3) := by simp
          replace o2: 3 * k + 2 ∈ A := by apply Set.mem_of_mem_of_subset o2 AB
          specialize H (3 * k + 2) (3 * k + 1)
          simp [o1,o2] at H
    -- Total blocks cover Icc 1 2015 --
    have h_cover : ∀ x ∈  Finset.Icc 1 2015, ∃ B ∈ blocks, x ∈ B := by
      intro x
      intro hx
      simp [blocks]
      simp at hx
      use ((x-1)/3: ℕ)
      constructor
      . omega
      . simp [g,f]
        have ineq: (x - 1) / 3 ≤ 671 := by omega
        simp [ineq]
        omega
    -- Calculate the bound --
    have h_bound : A.card ≤ blocks.card := by
      -- rw [← Finset.card_univ] --
      -- define the injective map --
      let F: ℕ → Finset ℕ := fun k => Finset.Icc (3 * ((k - 1)/3: ℕ)  + 1) (min (3 * ((k - 1)/3: ℕ)  + 3) 2015)
      apply Finset.card_le_card_of_injOn F
      intro k
      intro hk
      simp [F,blocks]
      use (k - 1)/3
      constructor
      . replace hk: k ∈ Finset.Icc 1 2015 := by apply Set.mem_of_mem_of_subset hk hA
        simp at hk
        omega
      . simp [g,f]
        intro o
        have ineqk: k ≤ 2015 := by
          replace hk: k ∈ Finset.Icc 1 2015 := by apply Set.mem_of_mem_of_subset hk hA
          simp at hk
          omega
        omega
      rw [Set.injOn_iff_injective]
      simp [Finset.Icc]
      intro k1 k2 eq
      obtain ⟨s1,k1⟩ := k1
      obtain ⟨s2,k2⟩ := k2
      simp [Finset.restrict] at eq
      simp [Subtype.ext_iff]
      simp [F] at eq
      have s1bound: s1 ∈ Finset.Icc 1 2015 := by
        apply Set.mem_of_mem_of_subset k1 hA
      simp at s1bound
      have s2bound: s2 ∈ Finset.Icc 1 2015 := by
        apply Set.mem_of_mem_of_subset k2 hA
      simp at s2bound
      -- construct a block B, use s1 and s2 belongs to A ⋂ B to get a contradiction --
      let B:= Finset.Icc (3 * ((s1 - 1) / 3) + 1) ((3 * ((s1 - 1) / 3) + 3) ⊓ 2015)
      have B_block: B ∈ blocks := by
        simp [blocks]
        use (s1 - 1) / 3
        constructor
        . omega
        . simp [g,f]
          have s1bound2: (s1 - 1) / 3 ≤ 671 := by omega
          simp [s1bound2]
      -- show that s1,s2 ∈ B --
      have s1B: s1 ∈ B := by
        simp [B]
        omega
      have s2B: s2 ∈ B := by
        simp [B,eq]
        omega
      have s1AB: s1 ∈ A ∩ B := by
        simp [s1B,k1]
      have s2AB: s2 ∈ A ∩ B := by
        simp [s2B,k2]
      specialize h_block_intersection B
      simp [B_block] at h_block_intersection
      rw [Finset.card_le_one] at h_block_intersection
      specialize h_block_intersection s1
      simp [s1AB] at h_block_intersection
      specialize h_block_intersection s2
      simp [k2,s2B] at h_block_intersection
      exact h_block_intersection
    rw [blockcard] at h_bound
    exact h_bound
  constructor
  . simp
    let S : Finset ℕ := Icc 1 2015 |>.filter (fun x => x % 3 = 1)
  -- a technical counting lemma proved by using Finset.card_map, i.e. one to one map between finsets --
    have cardinality_filtered_set : S.card = 672 := by
  -- Step 1: The filtered set is {1, 4, 7, ..., 2014}
      have h_filter_eq : S = (Finset.range 672).map ⟨fun k => 1 + 3 * k, by
        intro a b hab
        simp at hab
        exact hab⟩ := by
        ext x
        simp [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_map]
        constructor
        · intro ⟨hx, hmod⟩
          have dvd: 3 ∣ x + 2 := by omega
          apply exists_eq_mul_right_of_dvd at dvd
          obtain ⟨t,ht⟩:= dvd
          have ht1: 1 ≤ t := by
            omega
          let a:= t - 1
          rw [show t = a + 1 by omega] at ht
          replace ht: x = 3 * a + 1 := by omega
          have ha: a < 672 := by
            by_contra! ha
            omega
          use a
          omega
        · rintro ⟨k, hk_mem, rfl⟩
          have h_le : k < 672 := by simpa using hk_mem
          have h_ub : 1 + 3 * k ≤ 2015 := by
            rw [Nat.lt_succ_iff] at h_le
            linarith
          refine ⟨⟨by linarith, h_ub⟩, by simp⟩
      -- Step 2: The cardinality is preserved under this bijection
      rw [h_filter_eq, Finset.card_map, Finset.card_range]
    use S
    constructor
    . apply Finset.filter_subset
    . constructor
      . intro a b
        intro ha
        intro hb
        intro ab
        simp [S] at ha
        rcases ha with ⟨j,k⟩
        simp [S] at hb
        rcases hb with ⟨r,s⟩
        have mod3: 3 ∣ a - b := by
          omega
        have nemod3: 3 ∣ a + b + 1 := by
          omega
        by_contra! d
        have contra: 3 ∣ a + b := by
          apply Nat.dvd_trans mod3 d
        omega
      . symm
        exact cardinality_filtered_set
  . intro k
    simp
    intro A
    specialize max_subset_size A
    intro hA
    intro h
    simp [hA,h] at max_subset_size
    apply max_subset_size at h
    intro hk
    rw [hk]
    exact h
    