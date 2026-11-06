import Mathlib

open Real Classical Finset

/- We show that the number of unordered pairs is n.choose 2 -/
lemma card_of_unordered_pairs {n : ℕ} (S : Finset α) (hcard : S.card = n) :
    (S.powerset.filter (fun T => T.card = 2)).card = n.choose 2 := by
  -- We will prove this by induction on n.
  induction n generalizing S with
  | zero =>
    -- S = ∅, trivial
    have : S = ∅ := by exact card_eq_zero.mp hcard
    simp [this, filter_singleton]
  | succ n ih =>
    -- Otherwise, choose a ∈ S.
    -- Let S' = S.erase a, then S'.card = n and S = S' ∪ {a}.
    have ⟨a, ha⟩ : S.Nonempty := by
      apply card_pos.mp
      simp [hcard]
    let S' := S.erase a
    have hS' : S'.card = n := by
      rw [card_erase_of_mem ha, hcard]
      simp
    -- We divide the pairs into two cases:
    -- 1. Pairs that do not contain a, which are in S'.
    -- 2. Pairs that contain a, which are of the form {a, b} for some b ∈ S'.
    have : filter (fun T ↦ #T = 2) S.powerset = S'.powerset.filter (fun T ↦ #T = 2) ∪ S'.image (fun b => {a, b}) := by
      ext T
      simp
      constructor <;> intro hT
      · by_cases h : a ∈ T
        · right
          let T' := T.erase a
          have hT' : T'.card = 1 := by
            rw [card_erase_of_mem h, hT.2]
          obtain ⟨b, hb⟩ := card_eq_one.mp hT'
          have hb' : b ∈ T' := by rw [hb]; simp
          simp [T'] at hb'
          use b
          simp [S', hb'.1]
          split_ands
          · apply Set.mem_of_subset_of_mem hT.1
            exact hb'.2
          · apply eq_of_subset_of_card_le
            · intro x hx
              simp at hx
              rcases hx with hx | hx
              · simp [hx]
                exact h
              · simp [hx]
                exact hb'.2
            · rw [hT.2, card_insert_of_not_mem]
              · simp
              · simp
                apply Ne.symm hb'.1
        · have hT' : T ⊆ S' := by
            simp [S']
            refine subset_erase.mpr ⟨hT.1, h⟩
          left
          use hT', hT.2
      · rcases hT with hT | hT
        · constructor
          · apply subset_trans hT.1
            simp [S']
            exact erase_subset a S
          · exact hT.2
        · obtain ⟨b, hb, hT⟩ := hT
          rw [←hT]
          constructor
          · intro x hx
            simp at hx
            rcases hx with hx | hx
            · simp [hx]
              exact ha
            · simp [hx]
              simp [S'] at hb
              exact hb.2
          · apply card_eq_two.mpr
            use a, b
            simp [S'] at hb
            simp [Ne.symm, hb.1]
    -- Note that these two sets are disjoint.
    -- The card of first set is n.choose 2 by induction hypothesis.
    -- The card of second set is n, since we can choose b from S' in n ways.
    rw [this, card_union_of_disjoint, ih  _ hS', card_image_of_injective, hS', Nat.choose_succ_left]
    · simp; ring
    · simp
    · intro b₁ b₂ h
      simp at h
      have : b₁ ∈ ({a, b₂} : Finset _) := by rw [←h]; simp
      simp at this
      rcases this with hb | hb
      · simp [hb] at h ⊢
        have : b₂ ∈ ({a} : Finset _) := by rw [h]; simp
        simp at this
        simp [this]
      · exact hb
    · intro A hA hB x hx
      have h₁ := hA hx
      have h₂ := hB hx
      simp at h₁ h₂
      have ha : a ∈ x := by
        obtain ⟨b, hb⟩ := h₂
        rw [←hb.2]
        simp
      apply h₁.1 at ha
      simp [S'] at ha

/- If for any P in S, there are at least k points that have the same distance to P, then there are at least n * k.choose 2 distinct triples
  (A, B, P) such that AP = BP -/
lemma card_distinct_triples_ge_n_mul_k_choose_two {k n : ℕ} (S : Finset (EuclideanSpace ℝ (Fin 2))) (hcard : S.card = n)
    (hS : ∀ P ∈ S, ∃ d : ℝ, (S.filter (fun Q => dist P Q = d)).card ≥ k) :
    ((S.powerset ×ˢ S).filter (fun ⟨T, P⟩ => T.card = 2 ∧ ∃ d, ∀ Q ∈ T, dist P Q = d)).card ≥ n * k.choose 2 := by
  -- First, we define pairs to be all pairs of distinct points in S.
  let pairs : Finset (Finset (EuclideanSpace ℝ (Fin 2))) := S.powerset.filter (fun T => T.card = 2)
  -- The cardinality of pairs is n choose 2.
  have hcard_pairs : pairs.card = n.choose 2 := by apply card_of_unordered_pairs S hcard
  -- Let s be the set of all triples (A, B, P) such that A and B are distinct points in S and the distance from P to A equals the distance from P to B.
  let s := (S.powerset ×ˢ S).filter (fun ⟨T, P⟩ => T.card = 2 ∧ ∃ d, ∀ Q ∈ T, dist P Q = d)
  simp
  change #s ≥ n * k.choose 2

  -- Given a point P in S, let f(P) be the set of all pairs T in S such that they have the same distance d from P.
  let f (P : EuclideanSpace ℝ (Fin 2)) := S.powerset.filter (fun T => T.card = 2 ∧ ∃ d, ∀ Q ∈ T, dist P Q = d)

  -- s can be rewritten as the union of images of f over all points P in S.
  have hs_eq_image_f : s = S.biUnion (fun P => (f P).image (fun T => ⟨T, P⟩)) := by
    ext ⟨T, P⟩
    simp [s, f, pairs]
    constructor <;> intro h
    · use P, h.1.2, T
      simp [h.1.1, h.2.1, h.2.2]
    · obtain ⟨P, hP, T, hT, h⟩ := h
      rw [←h.1, ←h.2]
      simp [hP, hT.1, hT.2.1, hT.2.2]

  -- Then #s = ∑ P ∈ S, #(f P), since f is injective.
  rw [hs_eq_image_f, card_biUnion]
  trans ∑ _ ∈ S, k.choose 2
  · -- We only need to show that #(f P) ≥ k.choose 2 for each P in pairs.
    apply sum_le_sum
    intro A hA
    rw [card_image_of_injective]
    · simp [f]
      -- According to the hypothesis, for each point P in S, there exists at least k points in S that have the same distance to P.
      obtain ⟨d, hd⟩ := hS A hA
      trans (#(filter (fun Q ↦ dist A Q = d) S)).choose 2
      · exact Nat.choose_le_choose 2 hd
      · -- Therefore, by our first lemma, the number of pairs T in S such that dist A T = d is at least k.choose 2.
        rw [←card_of_unordered_pairs (n := #(filter (fun Q ↦ dist A Q = d) S)) _ rfl]
        apply card_le_card
        intro T hT
        simp at hT ⊢
        obtain ⟨h₁, h₂⟩ := hT
        simp [h₂]
        constructor
        · apply subset_trans h₁
          exact filter_subset (fun Q ↦ dist A Q = d) S
        · use d
          intro Q hQ
          apply h₁ at hQ
          simp at hQ
          exact hQ.2
    · exact Prod.mk.inj_right A
  · apply le_of_eq
    simp [hcard]
  · intro T₁ h₁ T₂ h₂ h
    apply disjoint_left.mpr
    intro A hA
    simp at hA ⊢
    obtain ⟨P, hP, hA⟩ := hA
    intro Q hQ
    simp [←hA]
    apply Ne.symm (a := T₁) at h
    simp [h]

/- If AP=AQ, then A is on the perpendicular bisector of PQ. -/
lemma inner_eq_zero_of_dist_eq {a P Q : EuclideanSpace ℝ (Fin 2)} (ha : dist a P = dist a Q) : inner (P - Q) (a - (1 / 2 : ℝ) • (P + Q)) = (0 : ℝ) := by
  have : P - Q = (a - Q) - (a - P) := by simp
  rw [this]
  have : a - (1 / 2 : ℝ) • (P + Q) = (1 / 2 : ℝ) • (a - Q + (a - P)) := by module
  rw [this, inner_smul_right, inner_add_right, inner_sub_left, inner_sub_left (a - Q), real_inner_self_eq_norm_sq]
  rw [real_inner_self_eq_norm_sq, real_inner_comm]
  simp
  apply sub_eq_zero.mpr
  simp [dist_eq_norm] at ha
  rw [ha]

/- Any three points which have equal distant from P and Q are colliner. -/
lemma collinear_of_dist_eq {a b c P Q: EuclideanSpace ℝ (Fin 2)} (ha : dist a P = dist a Q) (hb : dist b P = dist b Q)
    (hc : dist c P = dist c Q) (hPQ : P ≠ Q) (ha' : a ≠ (1 / 2 : ℝ) • (P + Q)) : Collinear ℝ {a, b, c} := by

  -- We first construct a basis for the plane spanned by P and Q using P - Q and a - (1 / 2 : ℝ) • (P + Q).
  let basisVec := ![P - Q, a - (1 / 2 : ℝ) • (P + Q)]
  have hproduct : inner (P - Q) (a - (1 / 2 : ℝ) • (P + Q)) = (0 : ℝ) := by apply inner_eq_zero_of_dist_eq ha

  have hinner₀ : inner (P - Q) (basisVec 0) ≠ (0 : ℝ) := by
    intro h
    apply inner_self_eq_zero.mp at h
    apply sub_eq_zero.mp at h
    simp [h] at hPQ
  have hinner₁ : inner (P - Q) (basisVec 1) = (0 : ℝ) := by exact hproduct

  -- It is easy to see that the basis vectors are linearly independent and orthogonal.
  have hindependent : LinearIndependent ℝ basisVec := by
    apply linearIndependent_of_ne_zero_of_inner_eq_zero
    · intro i
      fin_cases i
      all_goals simp [basisVec]
      · exact sub_ne_zero_of_ne hPQ
      · intro h
        apply sub_eq_zero.mp at h
        simp [h] at ha'
    · intro i j h
      fin_cases i
      all_goals fin_cases j
      all_goals simp at h
      all_goals unfold basisVec
      all_goals rw [←hproduct]
      · congr
      · rw [real_inner_comm]
        congr

  have : Nonempty (Fin 2) := by exact instNonemptyOfInhabited
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  let basis := basisOfLinearIndependentOfCardEqFinrank hindependent hcard

  -- Now we can express b - (1 / 2 : ℝ) • (P + Q) and c - (1 / 2 : ℝ) • (P + Q) as linear combinations of the basis vectors.
  -- Note that the inner product of P - Q with these linear combinations is zero, which means they are orthogonal to the line spanned by P and Q.
  -- Therefore, the first coefficient (wrt (P - Q)) of the linear combination must be zero.
  obtain h₁ := Basis.linearCombination_repr basis (b - (1 / 2 : ℝ) • (P + Q))
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h₁
  simp only [Fin.sum_univ_two] at h₁
  have hproduct_b : inner (P - Q) (b - (1 / 2 : ℝ) • (P + Q)) = (0 : ℝ) := by
    apply inner_eq_zero_of_dist_eq hb
  rw [←h₁] at hproduct_b
  rw [inner_add_right, inner_smul_right, inner_smul_right, hinner₁, mul_zero, add_zero] at hproduct_b
  apply mul_eq_zero.mp at hproduct_b
  simp only [hinner₀, or_false] at hproduct_b
  rw [hproduct_b, zero_smul, zero_add] at h₁

  obtain h₂ := Basis.linearCombination_repr basis (c - (1 / 2 : ℝ) • (P + Q))
  rw [coe_basisOfLinearIndependentOfCardEqFinrank, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at h₂
  simp only [Fin.sum_univ_two] at h₂
  have hproduct_c : inner (P - Q) (c - (1 / 2 : ℝ) • (P + Q)) = (0 : ℝ) := by
    apply inner_eq_zero_of_dist_eq hc
  rw [←h₂] at hproduct_c
  rw [inner_add_right, inner_smul_right, inner_smul_right, hinner₁, mul_zero, add_zero] at hproduct_c
  apply mul_eq_zero.mp at hproduct_c
  simp only [hinner₀, or_false] at hproduct_c
  rw [hproduct_c, zero_smul, zero_add] at h₂

  -- Now we show that a, b, c can be expressed as r * (a - (1 / 2 : ℝ) • (P + Q)) + (1 / 2 : ℝ) • (P + Q)
  apply collinear_iff_exists_forall_eq_smul_vadd _ |>.mpr
  use (1 / 2 : ℝ) • (P + Q), a - (1 / 2 : ℝ) • (P + Q)
  intro p hp
  simp at hp
  rcases hp with hp | hp | hp <;> rw [hp]
  · use 1
    simp
  · use basis.repr (b - (1 / 2 : ℝ) • (P + Q)) 1
    trans b - (1 / 2 : ℝ) • (P + Q) + (1 / 2 : ℝ) • (P + Q)
    · module
    · nth_rw 1 [←h₁]
      simp only [vadd_eq_add]
      congr
  · use basis.repr (c - (1 / 2 : ℝ) • (P + Q)) 1
    trans c - (1 / 2 : ℝ) • (P + Q) + (1 / 2 : ℝ) • (P + Q)
    · module
    · nth_rw 1 [←h₂]
      simp only [vadd_eq_add]
      congr

/- 20. (NET 1) ${ }^{\text {IMO3 }}$ Given a set $S$ in the plane containing $n$ points and satisfying the conditions:
(i) no three points of $S$ are collinear,
(ii) for every point $P$ of $S$ there exist at least $k$ points in $S$ that have the same distance to $P$,
prove that the following inequality holds:  $$ k<\frac{1}{2}+\sqrt{2 n} $$ -/
theorem inequalities_24218 {n k : ℕ} (hn : 0 < n) (S : Finset (EuclideanSpace ℝ (Fin 2))) (hcard : S.card = n)
    (hS1 : ∀ P ∈ S, ∀ Q ∈ S, ∀ R ∈ S, P ≠ Q ∧ Q ≠ R ∧ P ≠ R → ¬Collinear ℝ {P, Q, R}) (hS2 : ∀ P ∈ S, ∃ d : ℝ, (S.filter (fun Q => dist P Q = d)).card ≥ k) :
    k < 1 / 2 + sqrt (2 * n) := by

  -- Prove by contradiction:
  -- Suppose that k ≥ 1 / 2 + sqrt (2 * n).
  by_contra h
  push_neg at h
  have hk_pos : k > 0 := by
    apply Nat.cast_lt (α := ℝ) |>.mp
    apply lt_of_lt_of_le ?_ h
    simp
    positivity

  -- Consider all the triplets (A, B, P) in S × S × S such that the distance from P to A equals the distance from P to B and A ≠ B.
  let s := (S.powerset ×ˢ S).filter (fun ⟨T, P⟩ => T.card = 2 ∧ ∃ d, ∀ Q ∈ T, dist P Q = d)

  -- Since given any point P in S, there are at least k points in S that have the same distance to P,
  -- the cardinality of s is at least k * (n chose 2).
  have hcard_s : s.card ≥ n * k.choose 2 := by
    apply card_distinct_triples_ge_n_mul_k_choose_two S hcard hS2

  -- Let t be the set of all unordered pairs of points in S.
  let t := S.powerset.filter (fun T => T.card = 2)

  -- The cardinality of t is n choose 2.
  have hcard_t : t.card = n.choose 2 := by
    apply card_of_unordered_pairs S hcard

  have hdvd {n : ℕ} : 2 ∣ n * (n - 1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by
        simp
        rw [Nat.mul_sub, mul_one]
        rw [show 2 * n = n + n by ring, ←add_assoc, Nat.sub_add_cancel]
        ring_nf
        exact Nat.le_mul_self n
      rw [this]
      apply Nat.dvd_add ih
      simp

  -- Then we can obtain that #s > 2#t, since k ≥ 1 / 2 + sqrt (2 * n).
  have hcard_gt : s.card > t.card * 2 := by
    apply lt_of_lt_of_le ?_ hcard_s
    rw [hcard_t, Nat.choose_two_right, Nat.choose_two_right]
    apply Nat.cast_lt (α := ℝ) |>.mp
    rw [Nat.cast_mul, Nat.cast_div, Nat.cast_mul, Nat.cast_sub, Nat.cast_mul, Nat.cast_div, Nat.cast_mul, Nat.cast_sub]
    · simp
      apply mul_lt_mul_of_pos_left
      · apply lt_of_lt_of_le (b := (1 / 2 + √(2 * n) ) * (1 / 2 + √(2 * n) - 1) / 2)
        · apply sub_pos.mp
          ring_nf
          rw [sq_sqrt]
          ring_nf
          norm_num
          simp
        · gcongr
          trans 1 / 2 + √(2 * 1) - 1
          · simp
            apply sub_nonneg.mp
            ring_nf
            rw [neg_div, neg_add_eq_sub]
            simp
            trans 1
            · norm_num
            · simp only [one_le_sqrt, Nat.one_le_ofNat]
          . gcongr
            simp
            exact hn
      · simp [hn]
    · exact hk_pos
    · apply hdvd
    . simp
    · exact hn
    · apply hdvd
    · simp

  -- Consider the projection of s onto the first component, which is a function from s to t.
  let proj (p : (Finset (EuclideanSpace ℝ (Fin 2))) × (EuclideanSpace ℝ (Fin 2))) := p.1
  have h_proj : ∀ p ∈ s, proj p ∈ t := by
    intro p hp
    simp [s] at hp
    simp [t, proj, hp.1.1, hp.2.1]

  -- Applying the pigeonhole principle, we can find a pair T:={P,Q} and three points a, b, c in S
  -- such that they all have the same distance to P and Q, i.e. dist(P, a) = dist(P, b) = dist(P, c) and dist(Q, a) = dist(Q, b) = dist(Q, c).
  obtain ⟨T, hT, hlt⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to h_proj hcard_gt
  simp [t] at hT
  obtain ⟨P, Q, hPQ, hT⟩ := card_eq_two.mp hT.2
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := two_lt_card.mp hlt
  simp [s, proj] at ha hb hc
  have hab : a.2 ≠ b.2 := by
    by_contra h
    have h' : a = b := by
      apply Prod.ext ?_ h
      simp [ha.2, hb.2]
    contradiction
  have hac : a.2 ≠ c.2 := by
    by_contra h
    have h' : a = c := by
      apply Prod.ext ?_ h
      simp [ha.2, hc.2]
    contradiction
  have hbc : b.2 ≠ c.2 := by
    by_contra h
    have h' : b = c := by
      apply Prod.ext ?_ h
      simp [hb.2, hc.2]
    contradiction

  -- Note that a b c are distinct points in S.
  have hsub : {a.2, b.2, c.2} ⊆ S := by
    intro x hx
    simp at hx
    rcases hx with hx | hx | hx <;> simp [hx]
    · exact ha.1.1.2
    · exact hb.1.1.2
    · exact hc.1.1.2
  -- Therefore {a.2, b.2, c.2} are not colinear.
  have : ¬ Collinear ℝ {a.2, b.2, c.2} := by apply hS1 a.2 ha.1.1.2 b.2 hb.1.1.2 c.2 hc.1.1.2 ⟨hab, hbc, hac⟩

  rw [ha.2] at ha
  rw [hb.2] at hb
  rw [hc.2] at hc

  have hdist {a : EuclideanSpace ℝ (Fin 2)} (h :  ∃ d, ∀ Q ∈ T, dist a Q = d) : dist a P = dist a Q := by
    obtain ⟨d, hd⟩ := h
    simp [hT] at hd
    rw [hd.1, hd.2]

  -- However, by our lemma, if a, b, c have the same distance to P and Q, they must be collinear.
  have : Collinear ℝ {a.2, b.2, c.2} := by
    by_cases h : a.2 = (1 / 2 : ℝ) • (P + Q)
    · have h : b.2 ≠ (1 / 2 : ℝ) • (P + Q) := by
        intro h'
        rw [←h'] at h
        contradiction
      apply collinear_of_dist_eq (hdist hb.1.2.2) (hdist hc.1.2.2) (hdist ha.1.2.2) hPQ at h
      have : ({b.2, c.2, a.2} : Set (EuclideanSpace ℝ (Fin 2))) = {a.2, b.2, c.2} := by
        ext x
        simp
        tauto
      rw [this] at h
      exact h
    · apply collinear_of_dist_eq (hdist ha.1.2.2) (hdist hb.1.2.2) (hdist hc.1.2.2) hPQ h
  -- This is a contradiction.
  contradiction
