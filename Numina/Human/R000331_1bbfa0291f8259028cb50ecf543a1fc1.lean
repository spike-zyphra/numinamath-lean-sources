import Mathlib

noncomputable def arithmetic_mean (a b : ℝ) : ℝ := (a + b) / 2

/-
  We use f : [1, n] → ℝ to store the intgers. Originally, f(x) = x for all x ∈ [1, n].
  f(x)=0 means this number is replaced in some move. MoveTo f g means f can move to g.
-/
def MoveTo (f g : Finset.Icc 1 n → ℝ) :=
  ∃ a b : Finset.Icc 1 n, a < b ∧ f a ≠ 0 ∧ f b ≠ 0 -- f(a) and f(b) have not been replced
  ∧ g a = ((f a) + (f b)) / 2 ∧ g b = 0 -- replace f(a) with (f(a)+f(b))/2 and f(b) with 0
  ∧ ∀ c, c ≠ a → c ≠ b → g c = f c -- other numbers stay the same

/-
  Let  $n \ge 3$  be a fixed integer.  The numbers  $1,2,3, \cdots , n$  are written on a board.
  In every move one chooses two numbers and replaces them by their arithmetic mean.
  This is done until only a single number remains on the board.
  Determine the least integer that can be reached at the end by an appropriate sequence of moves.

  (Theresia Eisenkölbl)
-/
theorem number_theory_8956 (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {y : ℕ | ∃ g : Finset.Icc 1 n → ℝ, Relation.TransGen MoveTo (fun x => x) g
      ∧ ∃ a : Finset.Icc 1 n, g a = y ∧ ∀ b ≠ a, g b = 0} 2 := by

  -- every non_zero number ≥ 1, and at least one > 1
  -- if finally we can a single number x, then x > 1 must hold
  let ge_1 (n : ℕ) (f : Finset.Icc 1 n → ℝ) := (∀ x, f x ≠ 0 → f x ≥ 1) ∧ ∃ x, f x > 1

  -- prove  ge_1 n (fun x => x), since 2 > 1
  have id_ge_1 (hn : n ≥ 3) : ge_1 n (fun x => x) := by
    constructor
    · intro ⟨x, hx⟩ _
      simp at hx
      simp [hx.left]
    · have : n ∈ Finset.Icc 1 n := by simp; exact Nat.one_le_of_lt hn
      use ⟨n, this⟩
      simp
      exact Nat.lt_of_succ_lt hn

  -- prove if  f -> g and ge_1 n f, then ge_1 n g
  have move_f_g_ge_1 (f g : Finset.Icc 1 n → ℝ) (hf : ge_1 n f) (hg : MoveTo f g) : ge_1 n g := by
    obtain ⟨hge, ⟨c, hc⟩⟩ := hf
    obtain ⟨a, ⟨b, ⟨hlt, ⟨hfa, ⟨hfb, ⟨hga, ⟨hgb, hstay⟩⟩⟩⟩⟩⟩⟩ := hg
    have hfa' : f a ≥ 1 := by exact hge a hfa
    have hfb' : f b ≥ 1 := by exact hge b hfb
    constructor
    · intro x hgc
      by_cases hax : x = a
      · nth_rw 1 [<-hax] at hga
        simp [hga]
        calc
          (f a + f b) / 2 ≥ (1 + 1) / 2 := by rel [hfa', hfb']
          _ = 1 := by simp
      · by_cases hbx : x = b
        · rw [<-hbx] at hgb
          contradiction
        · apply hstay x hax at hbx
          rw [hbx]
          have : f x ≠ 0 := by rw [<-hbx]; exact hgc
          exact hge x this
    · by_cases hac : c = a
      · use a
        nth_rw 1 [hac] at hc
        simp [hga]
        calc
          (f a + f b) / 2 ≥ (f a + 1) / 2 := by rel [hfb']
          _ > (1 + 1) / 2 := by rel [hc]
          _ = 1 := by simp
      · by_cases hbc : c = b
        · use a
          nth_rw 1 [hbc] at hc
          simp [hga]
          calc
            (f a + f b) / 2 ≥ (1 + f b) / 2 := by rel [hfa']
            _ > (1 + 1) / 2 := by rel [hc]
            _ = 1 := by simp
        · apply hstay c hac at hbc
          use c
          rw [hbc]
          exact hc

  -- prove by induction if  f = > g and ge_1 n f, then ge_1 n g
  have trans_f_g_ge_1 (f g : Finset.Icc 1 n → ℝ) (hf : ge_1 n f) (hg : Relation.TransGen MoveTo f g) : ge_1 n g := by
    induction hg using Relation.TransGen.head_induction_on
    · rename_i h hmove; exact move_f_g_ge_1 h g hf hmove
    · rename_i h₁ h₂ hmove _ ih
      apply move_f_g_ge_1 h₁ h₂ hf at hmove
      apply ih at hmove
      exact hmove

  -- [1 2 3 ... n - 3, n - 1, n - 1, 0]
  let two_n_minus_1 (n : ℕ) (j : Finset.Icc 1 n) : ℝ :=
    if j < n - 2 then j else
      if j < n then n - 1 else 0

  -- id_m_padding_0 n m = [1 2 3 ... m (m+2) 0 0 ... 0]
  let id_m_padding_0 (n m : ℕ) (j : Finset.Icc 1 n) : ℝ :=
    if j ≤ m  then j else
      if j = m + 1 then m + 2 else 0

  -- some facts about n
  have hn0 : n > 0 := by exact Nat.zero_lt_of_lt hn

  have hn1 : n ≥ 1 := by exact hn0

  have hn2 : n ≥ 2 := by exact Nat.le_of_succ_le hn

  have hnin1 : n ∈ Finset.Icc 1 n := by simp; exact Nat.one_le_of_lt hn

  have hnin2 : n - 2 ∈ Finset.Icc 1 n := by simp; exact Nat.le_sub_of_add_le hn

  have hnin3 : n - 1 ∈ Finset.Icc 1 n := by simp; refine Nat.le_sub_one_of_lt ?_; exact Nat.lt_of_succ_lt hn

  have hnsub1 : n - 3 + 2 = n - 1 := by
    rw [show (3 = 1 + 2) by decide, Nat.sub_add_eq, Nat.sub_add_cancel]
    exact (Nat.le_sub_one_iff_lt hn0).mpr hn

  have hnsub2 : n - 2 = n - 3 + 1 := by
      rw [show (3 = 2 + 1) by decide, Nat.sub_add_eq, Nat.sub_add_cancel]
      exact Nat.le_sub_of_add_le hn

  -- prove (fun x => x) -> (two_n_minus_1 n), i.e. choose n, n-2 ↦ n - 1
  have id_move_to_two_n_minus_1 : MoveTo (fun x => x) (two_n_minus_1 n) := by
    use ⟨n - 2, hnin2⟩, ⟨n, hnin1⟩
    simp [two_n_minus_1, if_pos hn0, hn0]
    split_ands
    · exact Nat.sub_ne_zero_iff_lt.mpr hn
    · exact Nat.not_eq_zero_of_lt hn
    · field_simp; ring
    · intro c ⟨hc1, hc2⟩ hneq1 hneq2 h
      have h0 : c < n := by exact Nat.lt_of_le_of_ne hc2 hneq2
      have h1 : c ≤ n - 1 := by refine (Nat.le_sub_one_iff_lt hn0).mpr h0
      have h2 : c ≥ n - 2 := by exact Nat.sub_le_of_le_add h
      have h3 : c > n - 2 := by exact Nat.lt_of_le_of_ne h2 fun a ↦ hneq1 (Eq.symm a)
      have h4 : c = n - 1 := by refine Nat.le_antisymm h1 <| Nat.le_of_pred_lt h3
      simp [if_pos h0, h4, if_pos hn0]
      exact Eq.symm (Nat.cast_pred hn0)

  -- prove (two_n_minus_1 n) -> (id_m_padding_0 n (n - 3)), i.e., choose  n-1, n-1 ↦ n - 1
  have two_n_minus_1_move_to_one : MoveTo (two_n_minus_1 n) (id_m_padding_0 n (n - 3)) := by
    use ⟨n - 2, hnin2⟩, ⟨n - 1, hnin3⟩
    have hn3 : ¬ n ≤ n - 3 + 2 := by rw [hnsub1]; push_neg; exact Nat.sub_one_lt_of_lt hn
    have hn5 : ¬ n ≤ n - 3 + 1 := by push_neg; rw [<-hnsub2]; refine Nat.sub_lt hn0 ?_; trivial
    simp [two_n_minus_1, id_m_padding_0, hn0]
    split_ands
    · exact Nat.sub_succ_lt_self n 1 hn2
    · rw [<-Nat.cast_one, <-Nat.cast_sub hn1]; norm_cast; exact Nat.sub_ne_zero_iff_lt.mpr hn2
    · simp [if_neg hn3, if_pos hnsub2]; norm_cast
    · simp [if_neg hn5]; intro hn; linarith [hn3]
    · intro c ⟨hc1, hc2⟩ hneq1 hneq2
      by_cases hc : c ≤ n - 3
      · simp [if_pos hc]
        have : c < n - 2 := by rw [hnsub2]; apply Nat.lt_add_one_iff.mpr hc
        simp [if_pos this]
      · simp [if_neg hc]
        rw [<-hnsub2]
        simp [if_neg hneq1]
        have : c ≥ n - 2 := by push_neg at hc; rw [hnsub2]; exact hc
        have hc : ¬ c < n - 2 := by push_neg; exact this
        simp [if_neg hc]
        have : c > n - 2 := by exact Nat.lt_of_le_of_ne this fun a ↦ hneq1 (id (Eq.symm a))
        have : c ≥ n - 2 + 1 := by exact this
        rw [show (2 = 1 + 1) by simp, Nat.sub_add_eq, Nat.sub_add_cancel] at this
        have : c > n - 1 := by exact Nat.lt_of_le_of_ne this fun a ↦ hneq2 (id (Eq.symm a))
        have : ¬ c < n := by push_neg; exact Nat.le_of_pred_lt this
        simp [if_neg this]
        exact (Nat.le_sub_one_iff_lt hn0).mpr hn2

  -- prove (id_m_padding_0 n (m + 1)) -> (id_m_padding_0 n m), i.e. choose m + 1, m + 3 ↦ m + 2
  have id_m_plus_1_padding_0_move_to_m {m : ℕ} (hm : m + 2 ≤ n) : MoveTo (id_m_padding_0 n (m + 1)) (id_m_padding_0 n m) := by
    have h1 : m + 1 ∈ Finset.Icc 1 n := by simp; exact Nat.le_of_succ_le hm
    have h2 : m + 2 ∈ Finset.Icc 1 n := by simp [hm]
    use ⟨m + 1, h1⟩, ⟨m + 2, h2⟩
    simp [two_n_minus_1, id_m_padding_0]
    split_ands
    · norm_cast
    · norm_cast
    · field_simp; ring
    · intro a _  hneq1 hneq2
      by_cases ha : a ≤ m
      · have ha' : a ≤ m + 1 := by exact Nat.le_add_right_of_le ha
        simp [if_pos ha, if_pos ha']
      · have ha' : a ≥ m + 1 := by push_neg at ha; exact ha
        have ha' : ¬ a ≤ m + 1 := by push_neg; exact Nat.lt_of_le_of_ne ha' fun a_1 ↦ hneq1 (id (Eq.symm a_1))
        simp [if_neg ha, if_neg ha', if_neg hneq1, if_neg hneq2]

  -- prove by induction (fun x => x) => (id_m_padding_0 n m), therefore => (id_m_padding_0 n 0)
  have id_trans_to_m {m : ℕ} (hm : m ≤ n - 3) : Relation.TransGen MoveTo (fun x => x) (id_m_padding_0 n m) := by
    induction hm using Nat.decreasingInduction
    · rename_i k hk htrans
      have : MoveTo (id_m_padding_0 n (k + 1)) (id_m_padding_0 n k) := by
        apply id_m_plus_1_padding_0_move_to_m
        calc
          k + 2 ≤ n - 3 + 2 := by rel [hk]
          _ = n - 1 := by rw [show (3 = 1 + 2) by decide, Nat.sub_add_eq, Nat.sub_add_cancel]; exact Nat.le_sub_one_of_lt hn
          _ ≤ n := by exact Nat.sub_le n 1
      exact Relation.TransGen.tail htrans this
    · have hm1 : MoveTo (fun x => x) (two_n_minus_1 n) := by exact id_move_to_two_n_minus_1
      have hm2 : MoveTo (two_n_minus_1 n) (id_m_padding_0 n (n - 3)) := by exact two_n_minus_1_move_to_one
      have htrans : Relation.TransGen MoveTo (fun x => x) (two_n_minus_1 n) := by exact Relation.TransGen.single hm1
      exact Relation.TransGen.tail htrans hm2

  simp [IsLeast, lowerBounds]
  constructor
  · -- prove 2 is reachable, by (fun x => x) => (id_m_padding_0 n 0) and (id_m_padding_0 n 0) = [0 2 0 0 ...]
    use (id_m_padding_0 n 0)
    split_ands
    · exact id_trans_to_m <| Nat.le_sub_of_add_le hn
    · have : 1 ≤ 1 ∧ 1 ≤ n := by simp; exact Nat.one_le_of_lt hn
      use 1
      constructor
      · use this
        simp [id_m_padding_0]
      · intro b ⟨hge, hle⟩ hbneq
        have hb1 : b ≠ 0 := by exact Nat.not_eq_zero_of_lt hge
        simp [id_m_padding_0, if_neg hb1, hbneq]
  · -- prove any reachable single intgers > 1, therefore ≥ 2
    intro y g htrans a ha hay hunq
    obtain ⟨_, ⟨⟨c, hcin⟩, hc⟩⟩ := trans_f_g_ge_1 (fun x => x) g (id_ge_1 hn) htrans
    have hac : c = a := by
      by_contra hac
      apply hunq c at hac
      have : ¬ g ⟨c, hcin⟩ > 1 := by push_neg; rw [hac]; exact zero_le_one' ℝ
      contradiction
      simp at hcin
      exact hcin
    simp [<-hac] at hay
    rw [hay] at hc
    norm_cast at hc
