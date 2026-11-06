import Mathlib

open Classical

set_option maxHeartbeats 0

/- The graph of f and f (x - a) are disjoint iff ∀ x ∈ [a, 1], we have f x ≠ f (x - a) -/
lemma apply_ne_apply_of_disjoint_graph {graph_t : (ℝ → ℝ) → ℝ → Set (ℝ × ℝ)} (ht : ∀ a f, graph_t f a = Set.image (fun x => (x, f (x - a))) (Set.Icc a (a + 1))) {a : ℝ} (ha : a ∈ Set.Ioo 0 1) :
    Disjoint (graph_t f 0) (graph_t f a) ↔ ∀ x ∈ Set.Icc a 1, f x ≠ f (x - a) := by
  simp at ha
  constructor <;> intro h
  · by_contra h'
    simp at h'
    obtain ⟨x, hx₀, hx₁, hf⟩ := h'
    have h₁ : {(x, f x)} ≤ graph_t f 0 := by
      simp [ht]
      use x
      simp [hx₁]
      apply le_trans ?_ hx₀
      exact le_of_lt ha.1
    have h₂ : {(x, f x)} ≤ graph_t f a := by
      simp [ht]
      use x
      simp [hx₀, hf]
      apply le_trans hx₁
      simp
      exact le_of_lt ha.1
    apply h h₁ at h₂
    simp at h₂
  · refine Set.disjoint_left.mpr ?_
    intro ⟨x, y⟩ hmem
    simp [ht] at hmem ⊢
    obtain ⟨x, hx, hf⟩ := hmem
    intro x' hx₀' hx₁' hf'
    simp [hf', ←hf]
    apply Ne.symm
    apply h
    simp [hx]
    simp [hf, ←hf', hx₀']


/- If the graph of f and f(x-a) are disjoint, then the graphs of -f and -f (x - a) are also disjoint. -/
lemma disjoint_neg {graph_t : (ℝ → ℝ) → ℝ → Set (ℝ × ℝ)} (ht : ∀ a f, graph_t f a = Set.image (fun x => (x, f (x - a))) (Set.Icc a (a + 1))) :
    Disjoint (graph_t f 0) (graph_t f a) →  Disjoint (graph_t (-f) 0) (graph_t (-f) a) := by
  have hmap {a : ℝ} : graph_t (-f) a = (graph_t f a).image (fun x => (x.1, -x.2)) := by
    ext ⟨x, y⟩
    simp [ht]
  intro h
  rw [hmap, hmap]
  apply  Set.disjoint_image_iff ?_ |>.mpr h
  intro x y h
  simp at h
  exact Prod.ext_iff.mpr h

/- If the graph of f and f(x-a) are disjoint and f(a)>0, then f((n+1)a) > f(na) for any n such that (n + 1)a ≤ 1 -/
lemma apply_smul_strctmono_of_apply_a_pos {graph_t : (ℝ → ℝ) → ℝ → Set (ℝ × ℝ)} (ht : ∀ a f, graph_t f a = Set.image (fun x => (x, f (x - a))) (Set.Icc a (a + 1)))
    (hdis : Disjoint (graph_t f 0) (graph_t f a)) (hf₀ : f 0 = 0) (hf : f a > 0) (ha : a ∈ Set.Ioo 0 1) (hcon : ContinuousOn f (Set.Icc 0 1)) {n : ℕ} (hn : (n + 1) * a ≤ 1) :
    f ((n + 1) * a) > f (n * a) := by
  -- prove by induction on n
  induction n with
  | zero =>
    simp [hf₀]
    exact hf
  | succ n ih =>
    have hn' : (↑n + 1) * a ≤ 1 := by
      apply le_trans ?_ hn
      simp
      apply sub_nonneg.mp
      ring_nf
      simp at ha
      exact le_of_lt ha.1
    by_contra h
    -- If f (n * a) ≤ f((n+1)a)
    simp at h
    -- Let g(x)= f(x) - f(x-a)
    let g := fun x => f x - f (x - a)
    -- Note that g((n+2)a)≤ 0 < g((n+1)a)
    have hl : g ((n + 1) * a) > 0 := by
      simp [g]
      apply lt_of_eq_of_lt ?_ (ih hn')
      ring_nf
    have hr : g ((n + 2) * a) ≤ 0 := by
      simp [g]
      apply le_trans ?_ (le_trans h ?_)
      · apply le_of_eq
        ring_nf
      · apply le_of_eq
        ring_nf
    -- Note that g is continuous on ths interval.
    let s := Set.Icc ((n + 1) * a) ((n + 2) * a)
    have hcon : ContinuousOn g s := by
      simp [g]
      apply ContinuousOn.sub
      · have : s ⊆ Set.Icc 0 1 := by
          simp [s]
          intro x hx
          simp at hx ⊢
          constructor
          · apply le_trans ?_ hx.1
            apply mul_nonneg
            · positivity
            · simp at ha
              exact le_of_lt ha.1
          · apply le_trans hx.2
            apply le_of_eq_of_le ?_ hn
            simp
            left
            ring
        apply ContinuousOn.mono hcon this
      · apply ContinuousOn.comp (t := Set.Icc (n * a) ((n + 1) * a))
        · apply ContinuousOn.mono hcon
          intro x hx
          simp at hx ⊢
          constructor
          · apply le_trans ?_ hx.1
            apply sub_nonneg.mp
            ring_nf
            apply mul_nonneg
            · positivity
            · simp at ha
              exact le_of_lt ha.1
          · apply le_trans hx.2
            exact hn'
        · apply ContinuousOn.sub
          · exact continuousOn_id' s
          · apply continuousOn_const
        · intro x hx
          simp [s] at hx ⊢
          simp at ha
          constructor
          · apply le_sub_left_of_add_le
            apply le_trans ?_ hx.1
            apply le_of_eq
            ring
          · apply le_trans hx.2
            apply le_of_eq
            ring
    -- Applying the intermediate value theorem, we have ∃ x ∈ [(n+1)a, (n+2)a], f(x)=f(x-a)
    have : Set.Icc (g ((n + 2) * a)) (g ((n + 1) * a)) ⊆ g '' s := by
      simp at ha
      apply IsPreconnected.intermediate_value
      · exact isPreconnected_Icc
      · simp [s]
        apply sub_nonneg.mp
        ring_nf
        exact le_of_lt ha.1
      · simp [s]
        apply sub_nonneg.mp
        ring_nf
        exact le_of_lt ha.1
      · exact hcon
    have hmem : 0 ∈ Set.Icc (g ((n + 2) * a)) (g ((n + 1) * a)) := by
      simp [le_of_lt hl, hr]
    apply this at hmem
    obtain ⟨x, hx, hgx⟩ := hmem
    simp [g] at hgx
    apply sub_eq_zero.mp at hgx
    -- Therefore, the graphs of f(x) and f(x-a) are not disjoint, which is a contradiction.
    obtain hne := apply_ne_apply_of_disjoint_graph ht ha |>.mp hdis
    have : f x ≠ f (x - a) := by
      apply hne
      simp at ha
      simp [s] at hx ⊢
      constructor
      · apply le_trans ?_ hx.1
        apply sub_nonneg.mp
        ring_nf
        apply mul_nonneg
        · simp
        · exact le_of_lt ha.1
      · apply le_trans hx.2
        apply le_of_eq_of_le ?_ hn
        simp
        left
        ring
    contradiction

/- If the graph of f and f(x-a) are disjoint and f(a)>0, then f((n+1)a) > 0 for any n such that (n + 1)a ≤ 1 -/
lemma apply_smul_pos_of_apply_a_pos {graph_t : (ℝ → ℝ) → ℝ → Set (ℝ × ℝ)} (ht : ∀ a f, graph_t f a = Set.image (fun x => (x, f (x - a))) (Set.Icc a (a + 1)))
    (hdis : Disjoint (graph_t f 0) (graph_t f a)) (hf₀ : f 0 = 0) (hf : f a > 0) (ha : a ∈ Set.Ioo 0 1) (hcon : ContinuousOn f (Set.Icc 0 1)) {n : ℕ} (hn : (n + 1) * a ≤ 1) :
    f ((n + 1) * a) > 0 := by
  -- By induction on n
  induction n with
  | zero =>
    simp
    exact hf
  | succ n ih =>
    -- we have proved that f((n+1)*a) > f(n*a) >...>f(a)>0.
    have hn' : (↑n + 1) * a ≤ 1 := by
      apply le_trans ?_ hn
      simp
      apply sub_nonneg.mp
      ring_nf
      simp at ha
      exact le_of_lt ha.1
    apply lt_trans (ih hn')
    norm_cast
    apply lt_of_lt_of_eq (apply_smul_strctmono_of_apply_a_pos ht hdis hf₀ hf ha hcon hn)
    simp

/- If x is not in the closure of s, then ContinuousWithinAt f s x -/
lemma continuousWithinAt_of_notMem_closure_{α : Type u_1} {β : Type u_2} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {s : Set α} {x : α} (hx : x ∉ closure s) :
    ContinuousWithinAt f s x := by
  rw [mem_closure_iff_nhdsWithin_neBot, Filter.not_neBot] at hx
  rw [ContinuousWithinAt, hx]
  exact Filter.tendsto_bot

/- If s, t are closed, and f is continuous on s and t, then f is continuous on s ∪ t. -/
lemma union_of_closed {α : Type u_1} {β : Type u_2} [TopologicalSpace α] [TopologicalSpace β] {s t : Set α} {f : α → β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t) (hs : IsClosed s) (ht : IsClosed t) :
    ContinuousOn f (s ∪ t) := by
  refine fun x hx ↦ .union ?_ ?_
  · refine if hx : x ∈ s then hfs x hx else continuousWithinAt_of_notMem_closure_ ?_
    rwa [hs.closure_eq]
  · refine if hx : x ∈ t then hft x hx else continuousWithinAt_of_notMem_closure_ ?_
    rwa [ht.closure_eq]

/- Any function in the form of k (x - a) + b is continuous on any set s. -/
lemma continuousOn_affine {k b : ℝ} {s : Set ℝ} : ContinuousOn (fun x => k * (x - a) + b) s := by
  apply Continuous.continuousOn
  continuity

/- We show taht [0, 1] can be divided into two types of intervals: [(k * a) (1 - (n - k) * a))] and [(1 - (n - k) * a) ((k + 1) * a)] for appropriate k. -/
lemma Icc_eq_union {n : ℕ} {a : ℝ} (ha₀ : a > 0) (hn_mul : n * a < 1) : Set.Icc 0 (1 : ℝ) = Set.Icc (n * a) 1 ∪ ⋃ (k : Fin n), (Set.Icc (k * a) (1 - (n - k) * a)) ∪ Set.Icc (1 - (n - k) * a) ((k + 1) * a) := by
  ext x
  constructor <;> intro hx
  · by_contra h
    simp at hx h
    by_cases hx' : n * a ≤ x
    · apply h.1 at hx'
      linarith only [hx', hx.2]
    · simp at hx'
      let k := Nat.floor (x / a)
      have hk : k * a ≤ x := by
        have : k ≤ x / a := by
          apply Nat.floor_le
          apply div_nonneg
          · exact hx.1
          · positivity
        exact (le_div_iff₀ ha₀).mp this
      have hk_lt : k < n := by
        by_contra h
        simp at h
        have : ¬ x < n * a := by
          simp
          apply le_trans ?_ hk
          gcongr
        contradiction
      obtain h := h.2 ⟨k, hk_lt⟩
      simp at h
      apply h.1 at hk
      apply le_of_lt at hk
      simp at hk
      apply h.2 at hk
      have : ¬ (k + 1) * a < x := by
        simp
        apply le_of_lt
        have : k + 1 > x / a := by
          exact Nat.lt_floor_add_one (x / a)
        exact (mul_inv_lt_iff₀ ha₀).mp this
      contradiction
  · rcases hx with hx | hx
    · constructor
      · apply le_trans ?_ hx.1
        positivity
      · apply le_trans hx.2
        simp
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨⟨k, hk⟩, hx⟩ := hx
      simp only [Set.mem_union] at hx
      rcases hx with hx | hx
      · constructor
        · apply le_trans ?_ hx.1
          positivity
        · apply le_trans hx.2
          simp
          apply mul_nonneg
          · simp
            exact le_of_lt hk
          · positivity
      · constructor
        · apply le_trans ?_ hx.1
          simp
          trans n * a
          · gcongr
            simp
          · exact le_of_lt hn_mul
        · apply le_trans hx.2
          trans n * a
          · gcongr
            norm_cast
          · exact le_of_lt hn_mul

/- If 0 < a < 1 and a ≠ 1 / n for any n, there exists f continuous on [0, 1] and f(0) = f(1) = 0 such that the graphs of f(x) and f(x-a) are disjoint. -/
lemma exists_continuousOn {graph_t : (ℝ → ℝ) → ℝ → Set (ℝ × ℝ)} (ht : ∀ a f, graph_t f a = Set.image (fun x => (x, f (x - a))) (Set.Icc a (a + 1))) (ha₀ : 0 < a)
    (ha₁ : a < 1) (h : ∀ (x : ℕ), 0 < x → ¬a = (↑x)⁻¹) :
    ∃ f, ContinuousOn f (Set.Icc 0 1) ∧ f 0 = 0 ∧ f 1 = 0 ∧ Disjoint (graph_t f 0) (graph_t f a) := by
  -- Take n = ⌊1/a⌋
  -- Then we have na ≤ 1 < (n + 1) *a
  let n := Nat.floor (1 / a)
  have hn : n ≤ 1 / a := by apply Nat.floor_le; simp [le_of_lt ha₀]
  have hn_mul : n * a < 1 := by
    apply lt_of_le_of_ne
    · exact (le_div_iff₀ ha₀).mp hn
    · by_contra h'
      have : a = (↑n)⁻¹ := by exact Eq.symm (DivisionMonoid.inv_eq_of_mul (↑n) a h')
      apply h n
      · by_contra h''
        simp at h''
        simp [h''] at h'
      · exact this
  have hn' : (n + 1) > 1 / a := by exact Nat.lt_floor_add_one (1 / a)
  have hn_mul' : (n + 1) * a > 1 := by exact (mul_inv_lt_iff₀ ha₀).mp hn'
  have : 1 - n * a ≠ 0 := by
    apply ne_of_gt
    simp
    exact hn_mul
  -- Choose f(x) = k on point k*a and f(x) = -k and point 1 - k * a
  -- Then extend $f$ to other values of $[0,1]$ by linear interpolation.
  let f (x : ℝ) :=
    if h : ∃ k : ℕ, x ∈ Set.Icc (k * a) (1 - (n - k) * a) then let k := h.choose; -n / (1 - n * a) * (x - k * a) + k
    else  if h' : ∃ k : ℕ, x ∈ Set.Icc (1 - (n - k) * a) ((k + 1) * a) then let k := h'.choose; (n + 1) / ((n + 1) * a - 1) * (x - (1 - (n - k) * a)) + k - n
    else 0
  use f
  split_ands
  · -- Since [0, 1] is a finite union of closed intervals
    -- and f is continuous on these intervals,
    -- we have that f is continuous on [0, 1].
    rw [Icc_eq_union ha₀ hn_mul]
    apply union_of_closed
    · let g (x : ℝ) := -↑n / (1 - ↑n * a) * (x - n * a) + n
      have hcongr : Set.EqOn f g (Set.Icc (↑n * a) 1) := by
        intro x hx
        simp [f, g]
        have : ∃ k : ℕ, ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by
          use n
          simp at hx
          simp
          exact hx
        simp [this]
        set k := this.choose with hk
        have hk_spec : ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by
          apply this.choose_spec
        have hk : k = n := by
          by_contra hc
          simp at hx
          rcases lt_or_gt_of_ne hc with hc | hc
          · have : ¬ x ≥ n * a := by
              simp
              apply lt_of_le_of_lt hk_spec.2
              apply lt_of_lt_of_le (b := (k + 1) * a)
              · apply sub_pos.mp
                ring_nf
                apply sub_pos.mpr at hn_mul'
                apply lt_of_lt_of_eq hn_mul'
                ring_nf
              · gcongr
                norm_cast
            exact this.elim hx.1
          · have : ¬ x ≤ 1 := by
              simp
              apply lt_of_lt_of_le ?_ hk_spec.1
              apply lt_of_lt_of_le (b := (n + 1) * a)
              · exact hn_mul'
              · gcongr
                norm_cast
            exact this.elim hx.2
        rw [hk]
      apply ContinuousOn.congr ?_ hcongr
      simp [g]
      apply continuousOn_affine
    · apply LocallyFinite.continuousOn_iUnion
      · apply locallyFinite_of_finite
      · intro _
        apply IsClosed.union
        · exact isClosed_Icc
        · exact isClosed_Icc
      · intro ⟨i, hi⟩
        simp
        apply union_of_closed
        · let g (x : ℝ) := -↑n / (1 - ↑n * a) * (x - ↑i * a) + i
          have hcongr : Set.EqOn f g (Set.Icc (↑i * a) (1 - (↑n - ↑i) * a)) := by
            intro x hx
            simp at hx
            simp [f, g]
            have : ∃ k : ℕ, ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by use i
            simp [this]
            set k := this.choose with hk
            have hk_spec : ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by
              apply this.choose_spec
            have hk : k = i := by
              by_contra hk
              rcases lt_or_gt_of_ne hk with hk | hk
              · have : ¬ i * a ≤ x := by
                  simp
                  apply lt_of_le_of_lt hk_spec.2
                  apply lt_of_lt_of_le (b := (k + 1) * a)
                  · apply sub_pos.mp
                    ring_nf
                    apply sub_pos.mpr at hn_mul'
                    apply lt_of_lt_of_eq hn_mul'
                    ring_nf
                  · gcongr
                    norm_cast
                exact this.elim hx.1
              · have : ¬ x ≤ 1 - (n - i) * a := by
                  simp
                  apply lt_of_lt_of_le ?_ hk_spec.1
                  apply lt_of_lt_of_le (b := (i + 1) * a)
                  · apply sub_pos.mp
                    ring_nf
                    apply sub_pos.mpr at hn_mul'
                    apply lt_of_lt_of_eq hn_mul'
                    ring_nf
                  · gcongr
                    norm_cast
                exact this.elim hx.2
            simp [hk]
          apply ContinuousOn.congr ?_ hcongr
          apply continuousOn_affine
        · let g (x : ℝ) := (↑n + 1) / ((↑n + 1) * a - 1) * (x - (1 - (↑n - ↑i) * a)) + (↑i - ↑n)
          have hcongr : Set.EqOn f g (Set.Icc (1 - (↑n - ↑i) * a) ((↑i + 1) * a)) := by
            intro x hx
            simp at hx
            simp [f, g]
            by_cases h : ∃ k : ℕ, ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a
            · simp [h]
              set k := h.choose with hk
              have hk_spec : ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by apply h.choose_spec
              have hk : i = k ∨ k = i + 1 := by
                by_contra hk
                simp at hk
                rcases lt_or_gt_of_ne hk.1 with h | h
                · have : ¬ k * a ≤ x := by
                    simp
                    apply lt_of_le_of_lt hx.2
                    gcongr
                    norm_cast
                    apply lt_of_le_of_ne h
                    exact Ne.symm hk.2
                  exact this.elim hk_spec.1
                · have : ¬ x ≤ 1 - (n - k) * a := by
                    simp
                    apply sub_left_lt_of_lt_add
                    apply lt_of_le_of_lt hx.1
                    rw [add_comm]
                    gcongr
                  exact this.elim hk_spec.2
              have : (↑n + 1) * a - 1 ≠ 0 := by
                apply ne_of_gt
                simp
                exact hn_mul'
              rcases hk with hk | hk
              ·
                have hx : x = 1 - (↑n - ↑i) * a := by
                  simp [←hk] at hk_spec
                  apply le_antisymm hk_spec.2
                  apply sub_left_le_of_le_add
                  rw [add_comm]
                  exact hx.1
                simp [hx, hk]

                field_simp
                ring
              · have hx : x = (i + 1) * a := by
                  apply le_antisymm hx.2
                  norm_cast
                  rw [←hk]
                  exact hk_spec.1
                simp [hx, hk]
                field_simp
                ring
            · simp [h]
              have :  ∃ k : ℕ, 1 ≤ x + (↑n - ↑k) * a ∧ x ≤ (↑k + 1) * a := by use i
              simp [this]
              set k := this.choose with hk
              have hk_spec :  1 ≤ x + (↑n - ↑k) * a ∧ x ≤ (↑k + 1) * a := by
                apply this.choose_spec
              have hk : k = i := by
                by_contra hk
                rcases lt_or_gt_of_ne hk with hk | hk
                · have : ¬ 1 ≤ x + (↑n - ↑i) * a := by
                    simp
                    apply lt_of_le_of_lt (b := (k + 1) * a + (n - i) * a)
                    · gcongr
                      exact hk_spec.2
                    apply lt_of_le_of_lt (b := (↑k + 1) * a + (↑n - (k + 1)) * a)
                    · gcongr
                      norm_cast
                    · apply sub_pos.mp
                      ring_nf
                      simp
                      rw [mul_comm]
                      exact hn_mul
                  exact this.elim hx.1
                · have : ¬ x ≤ (i + 1) * a := by
                    simp
                    have h : x ≥ 1 - (n - k) * a := by
                      linarith only [hk_spec.1]
                    apply lt_of_lt_of_le ?_ h
                    apply lt_of_lt_of_le (b := 1 - (n - (i + 1)) * a)
                    · apply sub_pos.mp
                      ring_nf
                      simp
                      exact hn_mul
                    · gcongr
                      norm_cast
                  exact this.elim hx.2
              simp [hk]
              ring
          apply ContinuousOn.congr ?_ hcongr
          apply continuousOn_affine
        · exact isClosed_Icc
        · exact isClosed_Icc
    · exact isClosed_Icc
    · refine isClosed_iUnion_of_finite ?_
      intro i
      refine IsClosed.union ?_ ?_
      · exact isClosed_Icc
      · exact isClosed_Icc
  · -- f(0)= f(0*a)=0
    simp [f]
    have : ∃ k : ℕ, k * a ≤ 0 ∧ (↑n - k) * a ≤ 1 := by
      use 0
      simp
      exact le_of_lt hn_mul
    simp [this]
    have : this.choose = 0 := by
      have h : this.choose * a ≤ 0 ∧ (↑n - this.choose) * a ≤ 1 := by
        apply this.choose_spec
      have h : this.choose ≤ 0 := by
        by_contra h'
        simp at h'
        have : this.choose * a > 0 := by positivity
        linarith only [this, h.1]
      simp at h
      exact h
    simp [this]
  · -- f(1) = f(1-0*a)=0
    simp [f]
    have : ∃ k : ℕ, ↑k * a ≤ 1 ∧ (↑n - ↑k) * a ≤ 0 := by
      use n
      constructor
      · apply le_of_lt
        exact hn_mul
      · simp
    simp [this]
    have : this.choose = n := by
      have h : this.choose * a ≤ 1 ∧ (↑n - this.choose) * a ≤ 0 := by
        apply this.choose_spec
      by_contra h'
      rcases lt_or_gt_of_ne h' with h' | h'
      · have : ¬ (n - this.choose) * a ≤ 0 := by
          simp
          apply mul_pos
          · simp [h']
          · exact ha₀
        exact this.elim h.2
      · have : ¬ this.choose * a ≤ 1 := by
          simp
          apply lt_of_lt_of_le hn_mul'
          gcongr
          norm_cast at h' ⊢
        exact this.elim h.1
    simp [this]
    field_simp
  · -- Finally, we only need to show that ∀ x ∈ [a, 1], f(x) ≠ f(x-a)
    apply apply_ne_apply_of_disjoint_graph ht ?_ |>.mpr
    · intro x hx
      simp at hx
      simp [f]
      -- We only need to show that f (x) > f(x-a)
      by_cases h : ∃ k : ℕ, ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a
      · -- If x ∈ [ka, 1-(n-k)a] for some k
        -- the result follows by calculation.
        simp [h]
        set k' := h.choose with hk'
        have hk'_spec : ↑k' * a ≤ x ∧ x ≤ 1 - (↑n - ↑k') * a := by
          apply h.choose_spec
        have hk'_pos : k' > 0 := by
          by_contra h
          simp at h
          simp [h] at hk'_spec
          have : ¬ x ≥ a := by
            simp
            apply lt_of_le_of_lt hk'_spec.2
            apply sub_left_lt_of_lt_add
            apply lt_of_lt_of_eq hn_mul'
            ring
          exact this.elim hx.1
        have ha : ∃ k : ℕ, ↑k * a ≤ x - a ∧ x ≤ 1 - (↑n - ↑k) * a + a := by
          use k' - 1
          constructor
          · apply le_sub_left_of_add_le
            apply le_trans ?_ hk'_spec.1
            apply le_of_eq
            rw [Nat.cast_sub hk'_pos]
            ring
          · apply le_trans hk'_spec.2
            apply le_of_eq
            rw [Nat.cast_sub hk'_pos]
            ring
        simp [ha]
        set k := ha.choose with hk
        have hk_spec : ↑k * a ≤ x - a ∧ x ≤ 1 - (↑n - ↑k) * a + a := by
          apply ha.choose_spec
        have hc : k' = k + 1 := by
          by_contra hc
          rcases lt_or_gt_of_ne hc with hc | hc
          · have : ¬ k * a ≤ x - a := by
              simp
              apply sub_left_lt_of_lt_add
              apply lt_of_le_of_lt hk'_spec.2
              apply lt_of_lt_of_le (b := (k' + 1) * a)
              · apply sub_pos.mp
                ring_nf
                apply sub_pos.mpr at hn_mul'
                apply lt_of_lt_of_eq hn_mul'
                ring_nf
              · simp [add_mul, add_comm]
                gcongr
                exact Nat.le_of_lt_succ hc
            exact this.elim hk_spec.1
          · have : ¬ x ≤ 1 - (↑n - ↑k) * a + a := by
              simp
              apply lt_of_lt_of_le ?_ hk'_spec.1
              have hc : k' ≥ k + 2 := by exact hc
              apply lt_of_lt_of_le (b := (k + 2) * a)
              · apply sub_pos.mp
                ring_nf
                apply sub_pos.mpr at hn_mul'
                apply lt_of_lt_of_eq hn_mul'
                ring_nf
              · gcongr
                norm_cast
            exact this.elim hk_spec.2
        rw [hc]
        field_simp
        intro heq
        apply sub_eq_zero.mpr at heq
        ring_nf at heq
        apply sub_eq_zero.mp at heq
        simp [heq] at hn_mul
      · -- If x ∈ [1-(n-k )a, (k + 1)a] for some k,
        -- we follow a similar argument.
        simp [f, h]
        have ha : ¬ ∃ k : ℕ, ↑k * a ≤ x - a ∧ x ≤ 1 - (↑n - ↑k) * a + a := by
          by_contra ha
          obtain ⟨k, hk⟩ := ha
          have : ∃ k : ℕ, ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by
            use k + 1
            constructor
            · obtain h := hk.1
              apply add_le_of_le_sub_left at h
              apply le_trans ?_ h
              simp
              apply le_of_eq
              ring
            · apply le_trans hk.2
              simp
              apply le_of_eq
              ring
          contradiction
        simp [ha]
        by_cases h' : ∃ k : ℕ, 1 ≤ x + (↑n - k) * a ∧ x ≤ (k + 1) * a
        · simp [h']
          set k' := h'.choose with hk'
          have hk'_spec : 1 ≤ x + (↑n - k') * a ∧ x ≤ (k' + 1) * a := by
            apply h'.choose_spec
          by_cases hk_pos : k' = 0
          · simp [hk_pos] at hk'_spec
            have : x = a := by
              apply le_antisymm hk'_spec.2 hx.1
            simp [this]
            have : ∃ k : ℕ, ↑k * a ≤ x ∧ x ≤ 1 - (↑n - ↑k) * a := by
              use 1
              simp [this]
              apply sub_nonneg.mp
              ring_nf
              simp
              exact le_of_lt hn_mul
            contradiction
          have hk_pos : k' > 0 := by exact Nat.zero_lt_of_ne_zero hk_pos
          have ha : ∃ k : ℕ, 1 ≤ x - a + (↑n - k) * a ∧ x ≤ (k + 1) * a + a := by
            use k' - 1
            constructor
            · apply le_trans hk'_spec.1
              simp at hk'
              rw [Nat.cast_sub hk_pos]
              apply sub_nonneg.mp
              ring_nf
              simp
            · apply le_trans hk'_spec.2
              simp [hk_pos]
              apply sub_nonneg.mp
              ring_nf
              simp
          simp [ha]
          set k := ha.choose with hk
          have hk_spec : 1 ≤ x - a + (↑n - k) * a ∧ x ≤ (k + 1) * a + a := by
            apply ha.choose_spec
          have hc : k' = k + 1 := by
            by_contra hc
            rcases lt_or_gt_of_ne hc with hc | hc
            · have : ¬ 1 ≤ x - a + (↑n - k) * a := by
                simp
                apply lt_of_le_of_lt (b := (↑k' + 1) * a - a + (↑n - ↑k) * a)
                · gcongr
                  exact hk'_spec.2
                apply lt_of_le_of_lt (b := (↑k + 1) * a - a + (↑n - ↑k) * a)
                · gcongr
                  exact Nat.le_of_lt_succ hc
                · apply sub_pos.mp
                  ring_nf
                  rw [mul_comm]
                  simp [hn_mul]
              exact this.elim hk_spec.1
            · have : ¬ x ≤ (k + 1) * a + a := by
                simp
                apply lt_of_le_of_lt (b := (↑k' - 1) * a + a)
                · gcongr
                  trans ↑(k' - 1 : ℕ)
                  · norm_cast
                    exact (Nat.le_sub_one_iff_lt hk_pos).mpr hc
                  · rw [Nat.cast_sub hk_pos]
                    simp
                · apply sub_pos.mp
                  obtain h := hk'_spec.1
                  apply sub_nonneg.mpr at h
                  apply lt_of_le_of_lt h
                  apply sub_pos.mp
                  ring_nf
                  simp
                  rw [mul_comm]
                  exact hn_mul
              exact this.elim hk_spec.2
          rw [hc]
          field_simp
          intro heq
          apply sub_eq_zero.mpr at heq
          ring_nf at heq
          simp at heq
        · simp at h h'
          let k := Nat.floor (x / a)
          have : k * a ≤ x := by
            have : k ≤ x / a := by
              apply Nat.floor_le
              apply div_nonneg
              · apply le_trans ?_ hx.1
                apply le_of_lt
                exact ha₀
              · apply le_of_lt
                exact ha₀
            exact (le_div_iff₀ ha₀).mp this
          apply h at this
          apply lt_add_of_sub_right_lt at this
          apply le_of_lt at this
          apply h' at this
          have : ¬ (k + 1) * a < x := by
            simp
            apply le_of_lt
            have : k + 1 > x / a := by
              exact Nat.lt_floor_add_one (x / a)
            exact (mul_inv_lt_iff₀ ha₀).mp this
          contradiction
    · simp [ha₀, ha₁]



/-9. (NET) Let $f(x)$ be a continuous function defined on the closed interval $0 \leq x \leq 1$. Let $G(f)$ denote the graph of $f(x):
G(f)=\left\{(x, y) \in \mathbb{R}^{2} \mid 0 \leq\right.$ $x \leq 1, y=f(x)\}$. Let $G_{a}(f)$ denote the graph of the translated
function $f(x-a)$ (translated over a distance $a$ ), defined by $G_{a}(f)=\{(x, y) \in$ $\left.\mathbb{R}^{2} \mid a \leq x \leq a+1,
 y=f(x-a)\right\}$. Is it possible to find for every $a$, $0<  <1$,  a continuous function $f(x)$, defined on $0 \leq x \leq 1$,
 such that $f(0)=f(1)=0$ and $G(f)$ and $G_{a}(f)$ are disjoint point sets?-/
theorem other_25076 {graph_t : (ℝ → ℝ) → ℝ → Set (ℝ × ℝ)} (ht : ∀ a f, graph_t f a = Set.image (fun x => (x, f (x - a))) (Set.Icc a (a + 1))) :
    {a ∈ Set.Ioo 0 1 | ∃ f : ℝ → ℝ, ContinuousOn f (Set.Icc 0 1) ∧ f 0 = 0 ∧ f 1 = 0 ∧
    Disjoint (graph_t f 0) (graph_t f a)} = {a ∈ Set.Ioo (0 : ℝ) 1 | ¬ ∃ n : ℕ, n > 0 ∧ a = 1 / n} := by

  ext a
  simp
  intro ha₀ ha₁
  constructor <;> intro h
  · -- If n * a = 1 for some n, then wlog we assume f (a) > 0
    by_contra hn
    simp at hn
    obtain ⟨n, hn⟩ := hn
    obtain ⟨f, hcon, hf₀, hf₁, hdis⟩ := h
    wlog hf : f a > 0 generalizing f with H
    · -- Otherwise, consider -f, we can obtain the result since f(a) ≠ 0.
      apply H (-f)
      · exact continuousOn_neg_iff.mpr hcon
      · simp [hf₀]
      · simp [hf₁]
      · exact disjoint_neg ht hdis
      · simp at hf ⊢
        obtain hne := apply_ne_apply_of_disjoint_graph ht
        simp at hne
        obtain hne := hne ha₀ ha₁ |>.mp hdis
        -- If f(a)=0, then f(x) = f(x-a) at point x = a
        have ha : f a ≠ 0 := by
          obtain hne := hne a (by simp) (le_of_lt ha₁)
          simp [hf₀] at hne
          exact hne
        exact lt_of_le_of_ne hf ha
    · -- Now we have 0 < f(a) < f(2a) < ... < f(na)=f(1) = 0, which is a contradiciton.
      let n' := n - 1
      have hn' : (n' + 1) * a = 1 := by
        simp [hn, n']
        rw [mul_inv_cancel₀]
        simp
        apply ne_of_gt
        exact hn.1
      have hn'' : (n' + 1) * a ≤ 1 := by
        rw [hn']
      obtain h := apply_smul_pos_of_apply_a_pos ht hdis hf₀ hf (by simp [ha₀, ha₁]) hcon hn''
      simp [hn', hf₁] at h
  · -- Directly apply the lemma
    exact exists_continuousOn ht ha₀ ha₁ h
