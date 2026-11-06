import Mathlib
open Nat Real Finset Set

/- Soit ( $a_{n}$ ) une suite strictement croissante d'entiers positifs telle que $a_{1}=1$ et pour tout $n \geqslant 1, a_{n+1} \leqslant 2 n$. Montrer que pour tout entier $n \geqslant 1$, il existe deux indices $p$ et $q$ tels que $a_{p}-a_{q}=n$. -/
theorem number_theory_607418 (a : ℕ → ℕ) (ha : StrictMono a)
    (ha1 : a 1 = 1) (ha2 : ∀ n ≥ 1, a (n + 1) ≤ 2 * n) :
    ∀ n ≥ 1, ∃ p q, a p - a q = n := by 
  -- Prove for any $n ≥ 1$.
  intro n hn
  -- Construct $n$ pigeonholes ${i, n+i}$ for $i = 1, ..., n$ using the pigeonhole principle.
  let pigeonholes : Finset (Finset ℕ) := Finset.range n |>.image (fun i => {i + 1, n + i + 1})
  -- Verify that the pigeonholes are pairwise disjoint.
  have h_disjoint : Set.Pairwise (pigeonholes : Set (Finset ℕ)) Disjoint := by
    intro s1 hs1 s2 hs2 h_ne
    simp [pigeonholes, mem_image] at hs1 hs2
    rcases hs1 with ⟨i, hi, h_s1⟩
    rcases hs2 with ⟨j, hj, h_s2⟩
    rw [disjoint_iff]
    rw [← h_s1, ← h_s2]
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro x hx
    simp at hx
    rcases hx with ⟨h_x_i | h_x_ni, h_x_j | h_x_nj⟩
    · have h_ij : i = j := by linarith [h_x_i, h_x_j]
      have h_s1_eq_s2 : s1 = s2 := by rw [← h_s1, ← h_s2, h_ij]
      contradiction
    · have h_ij : i = n + j := by linarith [h_x_i, h_x_nj]
      linarith [hi]
    · have h_ij : n + i = j := by linarith [h_x_ni, h_x_j]
      linarith [hi]
    · have h_ij : i = j := by linarith [h_x_ni, h_x_nj]
      have h_s1_eq_s2 : s1 = s2 := by rw [← h_s1, ← h_s2, h_ij]
      contradiction
  -- Prove that if a pigeonhole contains two distinct elements $a_p$, $a_q$, then $a_p - a_q = n$ or $a_q - a_p = n$.
  have h_pigeonhole_diff : ∀ s ∈ pigeonholes, ∀ p q, a p ∈ s → a q ∈ s → p ≠ q → a p - a q = n ∨ a q - a p = n := by
    intro s hs p q h_ap h_aq h_ne
    simp [pigeonholes, Finset.mem_image] at hs
    rcases hs with ⟨i, hi, h_s⟩
    rw [← h_s] at h_ap h_aq
    simp at h_ap h_aq
    cases h_ap with
    | inl h_ap_i => cases h_aq with
      | inl h_aq_i =>
        have h_eq : a p = a q := by rw [h_ap_i, h_aq_i]
        have h_pq : p = q := by apply ha.injective; exact h_eq
        contradiction
      | inr h_aq_ni => right; rw [h_ap_i, h_aq_ni]; simp
    | inr h_ap_ni => cases h_aq with
      | inl h_aq_i => left; rw [h_ap_ni, h_aq_i]; simp
      | inr h_aq_ni =>
        have h_eq : a p = a q := by rw [h_ap_ni, h_aq_ni]
        have h_pq : p = q := by apply ha.injective; exact h_eq
        contradiction
  -- Prove that $a_1, ..., a_{n+1}$ lie in the interval $[1, 2n]$.
  have h_a_in_interval : ∀ m, 1 ≤ m → m ≤ n + 1 → a m ∈ Finset.Icc 1 (2 * n) := by
    intro m hm1 hm_n1
    induction m with
    | zero => linarith
    | succ m ih =>
      cases Nat.eq_or_lt_of_le hm1 with
      | inl h_m_1 =>
        have h_a_m : a (m + 1) = 1 := by rw [← h_m_1, ha1]
        rw [h_a_m]
        simp [Finset.mem_Icc]
        omega
      | inr h_m_gt_1 =>
      have h_m_ge_1 : m ≥ 1 := by omega
      have h_m_le_n : m ≤ n := by linarith [hm_n1]
      have h_m_pred : m ≥ 1 := by exact h_m_ge_1
      have h_a_succ : a (m + 1) ≤ 2 * m := by
        apply ha2 m h_m_pred
      have h_a_m_in : a (m + 1) ≤ 2 * n := by
        apply le_trans h_a_succ
        apply Nat.mul_le_mul_left
        exact h_m_le_n
      have h_a_1 : 1 ≤ a (m + 1) := by
        have h_a_1_le : a 1 ≤ a (m + 1) := ha.monotone (by linarith [hm1])
        rw [ha1] at h_a_1_le
        exact h_a_1_le
      simp [Finset.mem_Icc, h_a_1, h_a_m_in]
  -- Apply the pigeonhole principle: $a_1, ..., a_{n+1}$ are $n+1$ elements mapping into n pigeonholes.
  have h_pigeon : ∃ p q, p ≤ n + 1 ∧ q ≤ n + 1 ∧ p ≠ q ∧ ∃ s ∈ pigeonholes, a p ∈ s ∧ a q ∈ s := by
    let A : Finset ℕ := Finset.range (n + 1) |>.image (fun m => a (m + 1))
    have h_A_card : A.card = n + 1 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro x y h_eq
        have h_succ_eq : x + 1 = y + 1 := by apply ha.injective; exact h_eq
        exact Nat.succ_inj.mp h_succ_eq
    -- Prove that $A$ is a subset of the interval $[1, 2n]$
    have h_A_subset : A ⊆ Finset.Icc 1 (2 * n) := by
      intro x hx
      simp [A, Finset.mem_image] at hx
      rcases hx with ⟨m, hm, h_x⟩
      rw [← h_x]
      apply h_a_in_interval
      · simp
      · nlinarith [hm]
    -- Prove that the interval $[1, 2n]$ is covered by the union of pigeonholes.
    have h_pigeonholes_cover : Finset.Icc 1 (2 * n) ⊆ pigeonholes.biUnion id := by
      intro x hx
      simp [pigeonholes, Finset.mem_biUnion, Finset.mem_image]
      simp [Finset.mem_Icc] at hx
      cases Nat.le_total x n with
      | inl h_x_le_n =>
        cases Nat.lt_or_eq_of_le h_x_le_n with
        | inl h_x_lt_n =>
          use x - 1
          constructor
          · omega
          · omega
        | inr h_x_eq_n =>
          use n - 1
          constructor
          · omega
          · omega
      | inr h_n_le_x =>
        cases Nat.lt_or_eq_of_le h_n_le_x with
        | inl h_n_lt_x =>
          have h_x_le_2n : x ≤ 2 * n := hx.2
          use x - n - 1
          constructor
          · omega
          · right
            have h_eq : x = n + (x - n - 1) + 1 := by omega
            exact h_eq
        | inr h_n_eq_x =>
          use n - 1
          constructor
          · omega
          · omega
    -- Prove that the number of pigeonholes is $n$.
    have h_pigeonholes_card : pigeonholes.card = n := by
      simp [pigeonholes]
      rw [Finset.card_image_of_injective]
      · simp
      · intro x y h_eq
        have h_eq_simp : {x + 1, n + x + 1} = {y + 1, n + y + 1} := h_eq
        simp [Finset.ext_iff] at h_eq_simp
        have h_x_y : x + 1 = y + 1 ∨ x + 1 = n + y + 1 := by
          specialize h_eq_simp (x + 1)
          simp [Finset.mem_insert, Finset.mem_singleton] at h_eq_simp
          tauto
        have h_nx_y : n + x + 1 = y + 1 ∨ n + x + 1 = n + y + 1 := by
          specialize h_eq_simp (n + x + 1)
          simp [Finset.mem_insert, Finset.mem_singleton] at h_eq_simp
          tauto
        cases h_x_y
        · cases h_nx_y
          · linarith
          · linarith
        · cases h_nx_y
          · linarith
          · linarith
    -- Optimized pigeonhole proof: map elements of A to pigeonholes.
    let f : ℕ → Finset ℕ := fun a =>
      let candidates := Finset.filter (fun s => a ∈ s) pigeonholes
      if h : candidates.card = 1 then
        Classical.choose (by
          rw [Finset.card_eq_one] at h
          exact h)
      else ∅
    have h_a_in_pigeonhole : ∀ a ∈ A, ∃! s, s ∈ pigeonholes ∧ a ∈ s := by
      intro a ha
      -- Show there exists a pigeonhole containing $a$, using the covering property.
      have h_exists : ∃ s ∈ pigeonholes, a ∈ s := by
        have h_a_in_union : a ∈ pigeonholes.biUnion id := by
          apply h_pigeonholes_cover
          apply h_A_subset
          exact ha
        simp [Finset.mem_biUnion] at h_a_in_union
        exact h_a_in_union
      rcases h_exists with ⟨s, hs, h_a_s⟩
      exists s
      constructor
      · exact ⟨hs, h_a_s⟩
      · intro s' hs'
        rcases hs' with ⟨hs', h_a_s'⟩
        by_contra h_ne
        have h_ne':  s ≠ s' := by tauto
        have h_disj := h_disjoint hs hs' h_ne'
        simp [Finset.disjoint_iff_inter_eq_empty] at h_disj
        have h_a_inter : a ∈ s ∩ s' := by simp [h_a_s, h_a_s']
        have h_empty : s ∩ s' = ∅ := h_disj
        rw [h_empty] at h_a_inter
        simp at h_a_inter
    -- Prove that $f$ maps each $a ∈ A$ to a pigeonhole.
    have h_f_maps_to : ∀ a ∈ A, f a ∈ pigeonholes := by
      intro a ha
      have h_unique := h_a_in_pigeonhole a ha
      rcases h_unique with ⟨s, ⟨hs, h_a_s⟩, h_uniq⟩
      unfold f
      set candidates := Finset.filter (fun s => a ∈ s) pigeonholes
      have h_card_one : candidates.card = 1 := by
        apply Finset.card_eq_one.mpr
        exists s
        ext s'
        simp
        constructor
        · intro h_s'
          have h_s'_mem : s' ∈ pigeonholes ∧ a ∈ s' := Finset.mem_filter.mp h_s'
          have h_s'_eq_s : s' = s := h_uniq s' h_s'_mem
          exact h_s'_eq_s
        · intro h_s'
          rw [h_s']
          apply Finset.mem_filter.mpr
          exact ⟨hs, h_a_s⟩
      simp [h_card_one]
      -- Prove that the chosen candidate is $s$.
      have h_choose_eq_s : Classical.choose (Finset.card_eq_one.mp h_card_one) = s := by
        let h_exists := Finset.card_eq_one.mp h_card_one
        rcases Finset.card_eq_one.mp h_card_one with ⟨x, h_x⟩
        have h_s : x = s := by
          have h_x_mem : x ∈ candidates := by
            rw [h_x]
            simp
          have h_x_mem' : x ∈ pigeonholes ∧ a ∈ x := Finset.mem_filter.mp h_x_mem
          exact h_uniq x h_x_mem'
        have h_choose : candidates = {Classical.choose h_exists} := by
          exact Classical.choose_spec h_exists
        have h_choose_eq_x : Classical.choose h_exists = x := by
          have h_s_eq : {s} = candidates := by
            ext y
            constructor
            · intro h_y
              rw [Finset.mem_singleton] at h_y
              rw [h_y]
              apply Finset.mem_filter.mpr
              exact ⟨hs, h_a_s⟩
            · intro h_y
              have h_y_mem : y ∈ pigeonholes ∧ a ∈ y := Finset.mem_filter.mp h_y
              have h_y_eq_s : y = s := h_uniq y h_y_mem
              rw [Finset.mem_singleton]
              exact h_y_eq_s
          rw [h_x] at h_s_eq
          rw [h_choose] at h_x
          simp at h_x
          exact h_x
        rw [h_choose_eq_x]
        exact h_s
      rw [h_choose_eq_s]
      exact hs
    have h_f_a_in : ∀ a ∈ A, a ∈ f a := by
      intro a ha
      have h_unique := h_a_in_pigeonhole a ha
      rcases h_unique with ⟨s, ⟨hs, h_a_s⟩, h_uniq⟩
      unfold f
      set candidates := Finset.filter (fun s => a ∈ s) pigeonholes
      have h_card_one : candidates.card = 1 := by
        apply Finset.card_eq_one.mpr
        exists s
        ext s'
        simp
        constructor
        · intro h_s'
          have h_s'_mem : s' ∈ pigeonholes ∧ a ∈ s' := Finset.mem_filter.mp h_s'
          have h_s'_eq_s : s' = s := h_uniq s' h_s'_mem
          exact h_s'_eq_s
        · intro h_s'
          rw [h_s']
          apply Finset.mem_filter.mpr
          exact ⟨hs, h_a_s⟩
      simp [h_card_one]
      have h_choose_eq_s : Classical.choose (Finset.card_eq_one.mp h_card_one) = s := by
        let h_exists := Finset.card_eq_one.mp h_card_one
        rcases Finset.card_eq_one.mp h_card_one with ⟨x, h_x⟩
        have h_s : x = s := by
          have h_x_mem : x ∈ candidates := by
            rw [h_x]
            simp
          have h_x_mem' : x ∈ pigeonholes ∧ a ∈ x := Finset.mem_filter.mp h_x_mem
          exact h_uniq x h_x_mem'
        have h_choose : candidates = {Classical.choose h_exists} := by
          exact Classical.choose_spec h_exists
        have h_choose_eq_x : Classical.choose h_exists = x := by
          have h_s_eq : {s} = candidates := by
            ext y
            constructor
            · intro h_y
              rw [Finset.mem_singleton] at h_y
              rw [h_y]
              apply Finset.mem_filter.mpr
              exact ⟨hs, h_a_s⟩
            · intro h_y
              have h_y_mem : y ∈ pigeonholes ∧ a ∈ y := Finset.mem_filter.mp h_y
              have h_y_eq_s : y = s := h_uniq y h_y_mem
              rw [Finset.mem_singleton]
              exact h_y_eq_s
          rw [h_x] at h_s_eq
          rw [h_choose] at h_x
          simp at h_x
          exact h_x
        rw [h_choose_eq_x]
        exact h_s
      rw [h_choose_eq_s]
      exact h_a_s
    -- Prove that the number of pigeonholes $(n)$ is less than the number of elements in $A (n+1)$.
    have h_card_lt : pigeonholes.card < A.card := by
      rw [h_A_card, h_pigeonholes_card]
      exact Nat.lt_succ_self n
    -- Apply the pigeonhole principle: since $|A| > |pigeonholes|$, there exist distinct $p$, $q ∈ A$ mapping to the same pigeonhole.
    rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to h_card_lt h_f_maps_to with ⟨p, hp, q, hq, h_pq_ne, h_fp_eq_fq⟩
    simp [A, Finset.mem_image] at hp hq
    rcases hp with ⟨m, hm, h_p⟩
    rcases hq with ⟨m', hm', h_q⟩
    use m + 1, m' + 1
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · intro h_eq
      have h_m_eq : m = m' := by omega
      have h_a_eq : a (m + 1) = a (m' + 1) := by
        congr
      have h_pq_eq : p = q := by
        rw [← h_p, ← h_q, h_a_eq]
      contradiction
    · exists f p
      constructor
      · exact h_f_maps_to p (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, h_p⟩)
      · rw [h_fp_eq_fq]
        have h_p_in_A : p ∈ A := Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, h_p⟩
        have h_q_in_A : q ∈ A := Finset.mem_image.mpr ⟨m', Finset.mem_range.mpr hm', h_q⟩
        have h_ap_in_fp : a (m + 1) ∈ f p := by rw [h_p]; exact h_f_a_in p h_p_in_A
        have h_aq_in_fq : a (m' + 1) ∈ f q := by rw [h_q]; exact h_f_a_in q h_q_in_A
        have h_ap_in_fq : a (m + 1) ∈ f q := by rw [← h_fp_eq_fq]; exact h_ap_in_fp
        exact ⟨h_ap_in_fq, h_aq_in_fq⟩
  -- Use the pigeonhole principle to find $p$, $q$ such that $a_p - a_q = n$.
  rcases h_pigeon with ⟨p, q, h_p_n1, h_q_n1, h_ne, s, hs, h_ap, h_aq⟩
  have h_diff : a p - a q = n ∨ a q - a p = n := by
    apply h_pigeonhole_diff s hs p q h_ap h_aq h_ne
  cases h_diff with
  | inl h_diff => use p, q
  | inr h_diff => use q, p
