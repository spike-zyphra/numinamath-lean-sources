import Mathlib
open Mathlib
set_option maxHeartbeats 0

/-
  Let  $n \ge 3$  be a natural number.
  Determine the number  $a_n$  of all subsets of  $\{1, 2,...,n\}$
  consisting of three elements such that one of them is the arithmetic mean of the other two.
  *Proposed by Walther Janous*
-/

theorem number_theory_8916 (n : ℕ) (hn : n ≥ 3) :
    Set.ncard {s' : Set ℕ | s' ⊆ Finset.Icc 1 n ∧ ∃ a b c, s' = {a, b, c} ∧ b = (a + c) / (2 : ℚ) ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a}
    = (n - 1) * (n - 1) / 4 := by

  -- simplify the set into an easy form
  -- i.e., (a, b, c) | 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n ∧ 2 * b = a + c}
  have simplify : Set.ncard {s' : Set ℕ | s' ⊆ Finset.Icc 1 n ∧ ∃ a b c, s' = {a, b, c} ∧ b = (a + c) / (2 : ℚ) ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a} =
    Set.ncard {(a, b, c) : ℕ × ℕ × ℕ | 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n ∧ 2 * b = (a + c)} := by
    let t : Set <| ℕ × ℕ × ℕ := {(a, b, c) | 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n ∧ 2 * b = a + c}
    let s  := {s' : Set ℕ | s' ⊆ Finset.Icc 1 n ∧ ∃ a b c, s' = {a, b, c} ∧ b = (a + c) / (2 : ℚ) ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a}
    let f (i : ℕ × ℕ × ℕ) (_ : i ∈ t) : Set ℕ := {i.1, i.2.1, i.2.2}
    have hf' (i : ℕ × ℕ × ℕ) (hi : i ∈ t) : f i hi ∈ s := by
      obtain ⟨ha, ⟨hb, ⟨hc, ⟨hn, hmean⟩⟩⟩⟩ := hi
      simp [f]
      constructor
      · apply Set.insert_subset
        apply Finset.mem_Icc.mpr
        constructor <;> linarith
        apply Set.insert_subset
        apply Finset.mem_Icc.mpr
        constructor <;> linarith
        apply Set.singleton_subset_iff.mpr
        apply Finset.mem_Icc.mpr
        constructor <;> linarith
      · use i.1, i.2.1, i.2.2
        split_ands
        · trivial
        · field_simp
          norm_cast
          rw [Nat.mul_comm]
          exact hmean
        · exact Nat.ne_of_lt hb
        · exact Nat.ne_of_lt hc
        · have : i.1 < i.2.2 := by exact Nat.lt_trans hb hc
          exact Ne.symm (Nat.ne_of_lt this)
    have hf (a : Set ℕ) (ha : a ∈ s) : ∃ i, ∃ (h : i ∈ t), f i h = a := by
      obtain ⟨hsub, ⟨a, ⟨b, ⟨c, ⟨hs, ⟨hmean, ⟨hneq1, ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ := ha
      simp [hs] at hsub
      simp [Set.subset_def] at hsub
      obtain ⟨⟨ha1,ha2⟩, ⟨⟨_, _⟩, ⟨hc1, hc2⟩⟩⟩ := hsub
      by_cases h : a < b
      · field_simp at hmean
        norm_cast at hmean
        have : (a, b, c) ∈ t := by
          split_ands
          · exact ha1
          · exact h
          · linarith
          · exact hc2
          · rw [mul_comm]
            exact hmean
        use (a, b, c), this
        simp [f]
        exact Eq.symm hs
      · push_neg at h
        rcases Nat.le_iff_lt_or_eq.mp h with hlt | heq
        · have : (c, b, a) ∈ t := by
            field_simp at hmean
            norm_cast at hmean
            split_ands
            · exact hc1
            · linarith
            · exact hlt
            · exact ha2
            · rw [mul_comm, add_comm]
              exact hmean
          use (c, b, a), this
          simp [f, hs]
          refine Set.ext ?h.h
          intro x
          constructor <;> (intro hx; simp at hx ⊢; tauto)
        · simp [heq] at hneq1
    have h_inj (i j : ℕ × ℕ × ℕ) (hi : i ∈ t) (hj : j ∈ t) (hij : f i hi = f j hj) : i = j := by
      simp [f] at hij
      obtain ⟨_, ⟨hi2, ⟨hi3, ⟨_, _⟩⟩⟩⟩ := hi
      obtain ⟨_, ⟨hj2, ⟨hj3, ⟨_, _⟩⟩⟩⟩ := hj
      have : i.1 ∈ ({j.1, j.2.1, j.2.2} : Set ℕ) := by rw [<-hij]; exact Set.mem_insert i.1 {i.2.1, i.2.2}
      simp at this
      cases this with
      | inl h =>
        have hij' : {i.1, i.2.1, i.2.2} \ {i.1} = ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.1} := by rw [hij, h]
        simp at hij'
        have : i.2.1 ∈ ({j.2.1, j.2.2} : Set ℕ) \ {j.1} := by
          rw [<-hij']
          refine Set.mem_diff_singleton.mpr ?_
          constructor
          · exact Set.mem_insert i.2.1 {i.2.2}
          · exact Ne.symm (Nat.ne_of_lt hi2)
        simp at this
        cases this.left with
        | inl h2 =>
          have : {i.1, i.2.1, i.2.2} \ {i.1, i.2.1} = ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.1, j.2.1} := by rw [hij, h, h2]
          simp at this
          have : i.2.2 ∈ ({j.2.2} : Set ℕ) \ {j.1, j.2.1} := by
            rw [<-this]
            refine (Set.mem_diff i.2.2).mpr ?_;
            constructor
            · exact rfl
            · simp
              constructor
              · have :  i.1 < i.2.2 := by exact Nat.lt_trans hi2 hi3
                exact Nat.ne_of_lt' this
              · exact Nat.ne_of_lt' hi3
          simp at this
          have h3 := this.left
          exact Prod.ext_iff.mpr ⟨h,Prod.ext_iff.mpr ⟨h2, h3⟩⟩
        | inr h2 =>
          have : {i.1, i.2.1, i.2.2} \ {i.1, i.2.1} = ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.1, j.2.2} := by rw [hij, h, h2]
          simp only [ge_iff_le, Prod.forall, Prod.exists, or_true, true_and, Set.mem_insert_iff,
            Set.mem_singleton_iff, true_or, Set.insert_diff_of_mem] at this
          have : i.2.2 ∈ ({j.2.1, j.2.2} : Set ℕ) \ {j.1, j.2.2} := by
            rw [<-this]
            refine (Set.mem_diff i.2.2).mpr ?_;
            constructor
            · exact rfl
            · simp
              constructor <;> linarith
          simp [h2] at this
          cases this.left with
          | inl h3 =>
            have : ¬ j.2.1 < j.2.2 := by rw [<-h2, <-h3]; push_neg; exact Nat.le_of_succ_le hi3
            contradiction
          | inr h3 =>
            have : ¬ i.2.1 < i.2.2 := by rw [h3]; exact Eq.not_gt (Eq.symm h2)
            contradiction
      | inr h =>
        cases h with
        | inl h =>
          have : {i.1, i.2.1, i.2.2} \ {i.1} = ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.2.1} := by rw [hij, h]
          simp at this
          have : i.2.1 ∈ ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.2.1} := by
            rw [<-this]
            refine Set.mem_diff_singleton.mpr ?_
            constructor
            · exact Set.mem_insert i.2.1 {i.2.2}
            · exact Ne.symm (Nat.ne_of_lt hi2)
          obtain ⟨h2, h3⟩ := this
          cases h2 with
          | inl h2 =>
            have : ¬ i.1 < i.2.1 := by push_neg; rw [h2, h]; exact Nat.le_of_succ_le hj2
            contradiction
          | inr h2 =>
            cases h2 with
            | inl h2 => contradiction
            | inr h2 =>
              have : {i.1, i.2.1, i.2.2} \ {i.1, i.2.1} = ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.2.1, j.2.2} := by rw [hij, h, h2]
              simp at this
              have : i.2.2 ∈ ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.2.1, j.2.2} := by
                rw [<-this]
                refine (Set.mem_diff i.2.2).mpr ?_;
                constructor
                · exact rfl
                · simp
                  constructor <;> linarith
              simp [h2] at this
              obtain ⟨h3, ⟨h4, h5⟩⟩ := this
              cases h3 with
              | inl h3 =>
                have : ¬ i.2.2 > i.1 := by rw [h, h3]; linarith
                have : i.2.2 > i.1 := by linarith
                contradiction
              | inr h3 =>
                cases h3 with
                | inl h3 => contradiction
                | inr h3 => contradiction
        | inr h =>
          have : {i.1, i.2.1, i.2.2} \ {i.1} = ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.2.2} := by rw [hij, h]
          simp at this
          have : i.2.1 ∈ ({j.1, j.2.1, j.2.2} : Set ℕ) \ {j.2.2} := by
            rw [<-this]
            refine Set.mem_diff_singleton.mpr ?_
            constructor
            · exact Set.mem_insert i.2.1 {i.2.2}
            · exact Ne.symm (Nat.ne_of_lt hi2)
          obtain ⟨h2, h3⟩ := this
          cases h2 with
          | inl h2 =>
            have : ¬ i.1 < i.2.1 := by rw [h, h2]; linarith
            contradiction
          | inr h2 =>
            cases h2 with
            | inl h2 =>
              have : ¬ i.1 < i.2.1 := by rw [h, h2]; linarith
              contradiction
            | inr h2 => contradiction
    exact Eq.symm (Set.ncard_congr f hf' h_inj hf)

  rw [simplify]

  -- Let $s_n$ denote the the set of all triple satisfying the requirements
  -- To simplify the proof, we perform a translation n + 3
  let s (n : ℕ) := {(a, b, c) | 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ n + 3 ∧ 2 * b = a + c}

  -- We count by induction, so define the different $s_{n+1}-s_n$
  -- Note that there are two cases: n is odd/even
  -- We define them, respectively
  let s_even (n : ℕ) := {(a, b, c) | ∃ d, 1 ≤ d ∧ d ≤ n ∧ a = 2 * d ∧ c = 2 * n + 2 ∧ b = d + n + 1}
  let s_odd (n : ℕ) := {(a, b, c) | ∃ d, 1 ≤ d ∧ d ≤ n ∧ a = 2 * d - 1 ∧ c = 2 * n + 1 ∧ b = d + n}

  -- Compute the card of s_even
  -- It's trivial to compute by humans. But in lean4, we need to deal with some tedious details
  have card_even (n : ℕ) : (s_even n).ncard = n := by
    -- We show that |card_even n|=n by construct a bijection f : [n] → s_even n
    let f (i : ℕ) (hi : i < n) := (2 * i + 2, i + n + 2, 2 * n + 2)
    -- Show that f is a surjective
    have hf (a : ℕ × ℕ × ℕ) (h : a ∈ (s_even n)) : ∃ i, ∃ (h : i < n), f i h = a := by
      obtain ⟨d, ⟨hdge1, ⟨hdlen, ⟨hda, ⟨hcn, hb⟩⟩⟩⟩⟩ := h
      by_cases hn : n = 0
      · rw [hn] at hdlen
        linarith
      · push_neg at hn
        let i := d - 1
        have : i < n := by exact Nat.sub_one_lt_of_le hdge1 hdlen
        use i, this
        simp [f, i]
        apply Prod.ext_iff.mpr
        constructor
        · rw [hda, Nat.mul_sub, Nat.sub_add_cancel]
          simp
          exact hdge1
        · apply Prod.ext_iff.mpr
          constructor
          · simp [hb]
            calc
              d - 1 + n + 1 = (d - 1) + (n + 1) := by nth_rw 1 [<-Nat.add_assoc]
              _ = (d - 1) + 1 + n := by nth_rw 2 [add_comm]; rw [<-Nat.add_assoc]
              _ = d + n := by rw [Nat.sub_add_cancel hdge1]
          · simp [hcn]
    -- Show that f maps into s_even n
    have hf' (i : ℕ) (h : i < n ) : f i h ∈ (s_even n) := by
      simp [f]
      use i + 1
      constructor
      · exact Nat.le_add_left 1 i
      · constructor
        · exact h
        · constructor
          · linarith
          · constructor
            · ring
            · ring
    -- Show that f is a injective
    have f_inj (i j : ℕ) (hi : i < n) (hj : j < n) (hij : f i hi = f j hj) : i = j := by
      simp [f] at hij
      exact hij
    -- Done
    exact Set.ncard_eq_of_bijective f hf hf' f_inj

  -- Compute the card of s_odd
  -- Exactly the same maner with s_even
  have card_odd (n : ℕ) : (s_odd n).ncard = n := by
    let f (i : ℕ) (hi : i < n) := (2 * i + 1, i + n + 1, 2 * n + 1)
    have hf (a : ℕ × ℕ × ℕ) (h : a ∈ (s_odd n)) : ∃ i, ∃ (h : i < n), f i h = a := by
      obtain ⟨d, ⟨hdge1, ⟨hdlen, ⟨hda, ⟨hcn, hb⟩⟩⟩⟩⟩ := h
      by_cases hn : n = 0
      · rw [hn] at hdlen
        linarith
      · push_neg at hn
        let i := d - 1
        have : i < n := by exact Nat.sub_one_lt_of_le hdge1 hdlen
        use i, this
        simp [f, i]
        apply Prod.ext_iff.mpr
        constructor
        · rw [hda, Nat.mul_sub, mul_one]
          have : 2 * d - 1 ≥ 1 := by
            calc
              2 * d - 1 ≥ 2 * 1 - 1 := by rel [hdge1]
              _ ≥ 1 := by simp
          calc
            2 * d - 2 + 1 = 2 * d - 1 - 1 + 1 := by exact rfl
            _ = 2 * d - 1 := by rw [Nat.sub_add_cancel this]
        · apply Prod.ext_iff.mpr
          constructor
          · simp [hb]
            calc
              d - 1 + n + 1 = (d - 1) + (n + 1) := by nth_rw 1 [<-Nat.add_assoc]
              _ = (d - 1) + 1 + n := by nth_rw 2 [add_comm]; rw [<-Nat.add_assoc]
              _ = d + n := by rw [Nat.sub_add_cancel hdge1]
          · simp [hcn]
    have hf' (i : ℕ) (h : i < n ) : f i h ∈ (s_odd n) := by
      simp [f]
      use i + 1
      constructor
      · exact Nat.le_add_left 1 i
      · constructor
        · exact h
        · constructor
          · rw [Nat.mul_add]
            simp
          · constructor <;> ring
    have f_inj (i j : ℕ) (hi : i < n) (hj : j < n) (hij : f i hi = f j hj) : i = j := by
      simp [f] at hij
      exact hij
    exact Set.ncard_eq_of_bijective f hf hf' f_inj

  -- Show that $s_{sk+1}=s_{2k}∪(s_even k + 1)$ and  $s_{sk+2}=s_{2k+1}∪(s_even k + 2)$
  have s_cons (k : ℕ) : s (2 * k + 1) = (s <| 2 * k) ∪ (s_even <| k + 1) ∧ s (2 * k + 2) = (s <| 2 * k + 1) ∪ (s_odd <| k + 2) := by
    simp [s, s_even, s_odd]
    -- Firstly, show that $s_{sk+1}=s_{2k}∪(s_even k + 1)$
    constructor <;> (apply Set.ext; intro (a, b, c))
    · constructor <;> intro h
      -- We prove ∀ (a,b,c) ∈ s_{sk+1}, (a,b,c)∈ s_{2k}∪(s_even k + 1) -/
      · obtain ⟨hle1, ⟨hltb, ⟨hltc, ⟨hlek, habc⟩⟩⟩⟩ := h
        by_cases hc : c = 2 * k + 4
        · -- if c=2k+4, then (a,b,c)∈ (s_even k + 1)
          rw [hc] at hltc hlek habc ⊢
          apply Or.inr
          use  b - k - 2
          have habc : a = 2 * (b - k - 2) := by
            calc
              a = 2 * b - (2 * k + 4) := by exact Nat.eq_sub_of_add_eq (Eq.symm habc)
              _ = 2 * (b - k - 2) := by rw [Nat.sub_add_eq, Nat.mul_sub, Nat.mul_sub]
          constructor
          · -- otherwise, (a,b,c)∈ s_{2k}
            have : a ≥ 2 := by
              by_contra h
              push_neg at h
              have : a = 1 := by exact Nat.eq_of_le_of_lt_succ hle1 h
              have : 2 ∣ 1 := by rw [<-this, habc]; exact Nat.dvd_mul_right 2 (b - k - 2)
              contradiction
            rw [habc] at this
            linarith
          · split_ands
            all_goals linarith
        · push_neg at hc
          have hc : c ≤ 2 * k + 3 := by apply Nat.le_of_lt_succ <| Nat.lt_of_le_of_ne hlek hc
          apply Or.inl
          all_goals trivial
      · -- We prove s_{2k}∪(s_even k + 1) ⊆ s_{2k+1}, it's trivial
        cases h with
        | inl h =>
          obtain ⟨hle1, ⟨hltb, ⟨hltc, ⟨hlek, habc⟩⟩⟩⟩ := h
          split_ands
          all_goals linarith
        | inr h =>
          obtain ⟨d, ⟨hge1, ⟨hged, ⟨had, ⟨hck, hbd⟩⟩⟩⟩⟩ := h
          split_ands
          all_goals linarith
    · -- Secondly, show that $s_{sk+2}=s_{2k+1}∪(s_even k + 2)$ in the same manner
      constructor <;> intro h
      · obtain ⟨hle1, ⟨hltb, ⟨hltc, ⟨hlek, habc⟩⟩⟩⟩ := h
        by_cases hc : c = 2 * k + 5
        · rw [hc] at hltc hlek habc ⊢
          apply Or.inr
          use  b - k - 2
          have habc : a + 1 = 2 * (b - k - 2) := by
            calc
              a + 1 = a + 1 + (2 * k + 4) - (2 * k + 4) := by simp
              _ = a + (2 * k + 5) - (2 * k + 4) := by ring_nf
              _ = 2 * b - (2 * k + 4) := by rw [habc]
              _ = 2 * (b - k - 2)  := by rw [Nat.sub_add_eq, Nat.mul_sub, Nat.mul_sub]
          constructor
          · calc
              1 = (1 + 1) / 2 := by exact rfl
              _ ≤ (a + 1) / 2 := by rel [hle1]
              _ ≤ 2 * (b - k - 2) / 2 := by rw [habc]
              _ ≤ (b - k - 2) := by simp
          · constructor
            · linarith
            · constructor
              · exact Nat.eq_sub_of_add_eq habc
              · constructor
                · ring_nf
                · linarith
        · push_neg at hc
          have hc : c ≤ 2 * k + 4 := by apply Nat.le_of_lt_succ <| Nat.lt_of_le_of_ne hlek hc
          apply Or.inl
          all_goals trivial
      · cases h with
        | inl h =>
          obtain ⟨hle1, ⟨hltb, ⟨hltc, ⟨hlek, habc⟩⟩⟩⟩ := h
          split_ands
          all_goals linarith
        | inr h =>
          obtain ⟨d, ⟨hge1, ⟨hged, ⟨had, ⟨hck, hbd⟩⟩⟩⟩⟩ := h
          constructor
          · rw [had]
            calc
              1 = 2 * 1 - 1 := by exact rfl
              _ ≤ 2 * d - 1 := by rel [hge1]
          · constructor
            · rw [had, hbd]
              calc
                2 * d - 1 = d + d - 1 := by ring_nf
                _ ≤ d + (k + 2) - 1 := by rel [hged]
                _ < d + (k + 2) := by exact Nat.lt_add_one (d + (k + 2) - 1)
            · constructor
              · linarith
              · constructor
                · linarith
                · rw [hbd, had, hck]
                  ring_nf
                  rw [<-Nat.add_sub_assoc]
                  move_add [4, 5, <-d * 2]
                  trivial
                  calc
                    1 ≤ d := hge1
                    _ ≤ d + d := by exact Nat.le_add_right d d
                    _ ≤ d * 2 := by linarith

  -- Given $s_{sk+1}=s_{2k}∪(s_even k + 1)$ and  $s_{sk+2}=s_{2k+1}∪(s_even k + 2)$, we still need to prove that
  -- these two unions are disjoint unions, which is trivial.
  have s_disjoint (k : ℕ) : (Disjoint (s <| 2 * k) (s_even <| k + 1)) ∧ (Disjoint (s <| 2 * k + 1) (s_odd <| k + 2)) := by
    constructor <;>
    · apply Set.disjoint_iff_forall_ne.mpr
      intro (a₁, b₁, c₁) h₁ (a₂, b₂, c₂) h₂
      have hc₁ := h₁.right.right.right.left
      obtain ⟨d, ⟨_, ⟨_, ⟨_, ⟨hc₂⟩⟩⟩⟩⟩ := h₂
      by_contra heq
      simp at heq
      linarith

  -- The induction base $s_0$.
  -- We directly show that $s_0={(1,2,3)}$.
  have s_zero : s 0 = {(1, 2, 3)} := by
    apply Set.ext
    intro (a, b, c)
    constructor <;> intro hx
    · obtain ⟨ha, ⟨hb, ⟨hc, ⟨hxn, hmean⟩⟩⟩⟩ := hx
      have hceq3 : c = 3 := by
        apply Nat.le_antisymm
        · exact hxn
        · calc
            c ≥ b + 1 := by exact hc
            _ ≥ a + 2 := by simp; exact hb
            _ ≥ 3 := by simp; exact ha
      rw [hceq3] at hmean ⊢
      have hbeq2 : b = 2 := by
        apply Nat.le_antisymm
        · calc
            b ≤ c - 1 := by exact Nat.le_sub_one_of_lt hc
            _ ≤ 2 := by exact Nat.sub_le_of_le_add hxn
        · calc
            b ≥ a + 1 := by exact hb
            _ ≥ 2 := by simp; exact ha
      rw [hbeq2] at hmean ⊢
      have haeq1 : a = 1 := by linarith
      simp [haeq1]
    · rw [hx]
      simp [s]

  -- The main lemma.
  -- We prove by induction that $s_{2k} = (k+1)²$, $s_{2k+1}=k² + 3k + 2$
  have s_card (k : ℕ) : (s <| 2 * k).ncard = (k + 1) * (k + 1) ∧ (s <| 2 * k + 1).ncard = k * k + 3 * k + 2 := by
    induction k with
    | zero =>
      /- The base case. Apply lemma s_zero -/
      constructor
      · rw [s_zero]
        simp
      · rw [(s_cons 0).left]
        rw [Set.ncard_union_eq (s_disjoint 0).left ?_ ?_]
        rw [s_zero, card_even]
        simp
        · rw [s_zero]; exact Set.finite_singleton (1, 2, 3)
        · apply Set.finite_of_ncard_pos
          rw [card_even]
          trivial
    | succ k ih =>
      -- The induction step. We first deal with s_{2k}, which need to apply I.H.
      -- The key theorem is that if C=A∪B, A,B are finite and disjoint, then |C|=|A|+|B|
      have : (s (2 * (k + 1))).ncard = (k + 1 + 1) ^ 2 := by
        rw [mul_add, mul_one, (s_cons k).right, Set.ncard_union_eq (s_disjoint k).right ?_ ?_, ih.right, card_odd (k + 2)]
        · ring
        · apply Set.finite_of_ncard_pos
          rw [ih.right]
          linarith
        · apply Set.finite_of_ncard_pos
          rw [card_odd]
          linarith
      constructor
      · rw [this]; ring_nf
      · -- Then we deal with s_{2k}, which need to apply the result of s_{2k}, which is proved before
        rw [(s_cons <| k + 1).left, Set.ncard_union_eq (s_disjoint <| k + 1).left ?_ ?_, this, card_even (k + 2)]
        · ring
        · apply Set.finite_of_ncard_pos
          rw [this]
          linarith
        · apply Set.finite_of_ncard_pos
          rw [card_even]
          linarith

  --Now, combine the two case according the the parity of n - 3
  let k := n - 3
  by_cases hk : 2 ∣ k
  · -- If 2 ∣ n - 3, apply s_card (n - 3)/2, and simplify the result
    let k' := k / 2
    have : n = 2 * k' + 3 := by simp [k', Nat.mul_div_cancel' hk, k, Nat.sub_add_cancel hn]
    obtain res := (s_card (k / 2)).left
    simp only [s] at res
    rw [this, res, <-show k' = k / 2 by exact rfl]
    calc
      (k' + 1) * (k' + 1) = 4 * ((k' + 1) * (k' + 1)) / 4 := by simp
      _ = 2 * (k' + 1) * (2 * (k' + 1)) / 4 := by rw [<-Nat.mul_assoc]; move_mul [<-2, <-2]; simp
      _ = (2 * k' + 2) * (2 * k' + 2) / 4 := by exact rfl
  · -- otherwise, apply s_card (n - 4)/2, and simplify the result
    have hk' : k ≥ 1 := by
      by_contra hk'
      push_neg at hk'
      have : k = 0 := by exact Nat.lt_one_iff.mp hk'
      rw [this] at hk
      contradiction
    have hdvd : 2 ∣ (k - 1) := by exact (Nat.modEq_iff_dvd' hk').mp <| Eq.symm <| Nat.two_dvd_ne_zero.mp hk
    let k' := (k - 1) / 2
    have : n = 2 * k' + 4 := by
      calc
        n = k + 3 := by exact (Nat.sub_eq_iff_eq_add hn).mp rfl
        _ = 2 * k' + 1 + 3 := by simp [k', Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hk']
    obtain res := (s_card k').right
    simp only [s] at res
    rw [this, res]
    simp
    rw [add_mul, mul_add, mul_add, <-Nat.mul_assoc]
    move_mul [<-2, <-3, <-2]
    ring_nf
    apply Eq.symm
    calc
      (9 + k' * 12 + k' ^ 2 * 4) / 4 = (4 * (2 + k' * 3 + k' ^ 2) + 1) / 4 := by ring_nf
      _ = 2 + k' * 3 + k' ^ 2 := by rw[Nat.mul_add_div]; simp; trivial
