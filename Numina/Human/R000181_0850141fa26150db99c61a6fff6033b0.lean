import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat

/-
  Let  $n>2$  be an integer $.$  We want to color in red exactly  $n+1$  of the numbers  $1,2,\cdots,2n-1, 2n$  so that there do not exists three distinct red integers  $x,y,z$  satisfying  $x+y=z.$
  Prove that there is one and one only way to color the red numbers according to the given condition $.$
-/
theorem number_theory_8502 (n : ℕ) (hn : 2 < n) :
    ∃! red : Finset ℕ, red ⊆ Finset.Icc 1 (2 * n) ∧ red.card = n + 1 ∧
    ∀ x ∈ red, ∀ y ∈ red, ∀ z ∈ red, x ≠ y ∧ y ≠ z ∧ x ≠ z → x + y ≠ z := by
  -- n ... 2n is the only way
  use Finset.Icc n (2 * n)
  constructor
  · -- prove the correctness
    split_ands
    · -- subseteq Finset.Icc 1 (2 * n)
      intro x hx
      simp at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      constructor <;> linarith
    · -- card = n + 1
      simp
      rw [show 2 = 1 + 1 by simp, add_mul, one_mul, add_comm, <-Nat.add_assoc, Nat.add_sub_cancel, add_comm]
    · rintro x hx y hy z hz ⟨hxy, ⟨_, _⟩⟩
      -- prove x + y > 2 * n ≥ z
      simp at hx hy hz
      by_cases h : x < y
      · have : x + y > z := by
          calc
            x + y > x + x := by rel [h]
            _ ≥ n + n := by rel [hx.left]
            _ = 2 * n := by ring
            _ ≥ z := by rel [hz.right]
        exact Ne.symm (Nat.ne_of_lt this)
      · push_neg at h
        rcases lt_or_eq_of_le h with hlt | heq
        · have : x + y > z := by
            calc
              x + y > y + y := by rel [hlt]
              _ ≥ n + n := by rel [hy.left]
              _ = 2 * n := by ring
              _ ≥ z := by rel [hz.right]
          exact Ne.symm (Nat.ne_of_lt this)
        · simp [heq] at hxy
  · -- prove the uniqueness
    rintro red ⟨hsub, ⟨hcard, hneq⟩⟩
    suffices hge : ∀ x ∈ red, x ≥ n
    · -- if all elments in red ≥ n
      apply Finset.eq_of_subset_of_card_le
      · -- red ⊆ [n, 2n]
        intro x hx
        simp [hge x hx]
        obtain h := hsub hx
        simp at h
        simp [h]
      · -- red.card = [n, 2n].card
        apply Nat.le_of_eq
        simp [hcard]
        rw [show 2 = 1 + 1 by simp, add_mul, one_mul, add_comm, <-Nat.add_assoc, Nat.add_sub_cancel, add_comm]
    · -- prove by contradiction
      by_contra hin
      push_neg at hin
      obtain ⟨x, ⟨hin, hlt⟩⟩ := hin
      have : red.Nonempty := by use x
      -- obtain the maximum of red
      let d := red.max' this
      have d_max (x : ℕ) (hx : x ∈ red) : x ≤ d := by exact Finset.le_max' red x hx
      have d_in : d ∈ red := by exact Finset.max'_mem red this
      -- count the card of red
      let part₁ := Finset.filter (fun x => x ≠ d ∧ 2 * x ≠ d) red
      let f := fun x => d - x
      let part₂ : Finset ℕ := Finset.image f part₁
      -- part₁.card = part₂.card
      have hcard1 : part₂.card = part₁.card := by
        simp [part₂]
        apply Finset.card_image_of_injOn
        intro x₁ hx₁ x₂ hx₂ heq
        simp [f] at heq
        simp [part₁] at hx₁ hx₂ ⊢
        refine Int.ofNat_inj.mp ?_
        apply Int.sub_right_inj d |>.mp
        rw [<-Nat.cast_sub, <-Nat.cast_sub]
        · norm_cast
        · exact d_max x₂ hx₂.left
        · exact d_max x₁ hx₁.left
      -- part₁ ∪ part₂ ⊆ [1, d - 1]
      have hunion : part₁ ∪ part₂ ⊆ Finset.Icc 1 (d - 1) := by
        intro x hx
        simp at hx ⊢
        rcases hx with h | h
        · simp [part₁] at h
          obtain ⟨h1, ⟨h2, _⟩⟩ := h
          have : x ≤ d := by exact d_max x h1
          apply hsub at h1
          simp at h1
          constructor
          · exact h1.left
          · apply (Nat.le_sub_one_iff_lt ?_).mpr
            · exact Nat.lt_of_le_of_ne this h2
            · apply hsub at d_in
              simp at d_in
              exact d_in.left
        · simp [part₂] at h
          obtain ⟨a, ⟨h1, h2⟩⟩ := h
          simp [part₁] at h1
          simp [f] at h2
          rw [<-h2]
          constructor
          · apply le_sub_of_add_le
            have : a ≤ d := by exact d_max a h1.left
            apply one_add_le_iff.mpr
            exact Nat.lt_of_le_of_ne this h1.right.left
          · have : a ≥ 1 := by
              have h := h1.left
              apply hsub at h
              simp at h
              exact h.left
            rel [this]
      have hdisj : Disjoint part₁ part₂ := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx₁
        by_contra hx₂
        simp [part₂] at hx₂
        obtain ⟨a, ⟨hain, hfa⟩⟩ := hx₂
        simp [part₁] at hx₁ hain
        simp [f] at hfa
        have : x + a = d := by
          simp [<-hfa]
          rw [Nat.sub_add_cancel]
          exact d_max a hain.left
        have : ¬ x + a = d := by
          apply hneq x hx₁.left a hain.left d d_in
          split_ands
          · by_contra heq
            have : 2 * x = d := by
              calc
                2 * x = x + x := by ring
                _ = x + a := by rw [heq]
                _ = d := by exact this
            have : ¬ 2 * x = d := hx₁.right.right
            contradiction
          · exact hain.right.left
          · exact hx₁.right.left
        contradiction
      have hcard₁ : part₁.card ≤ (d - 1) / 2 := by
        apply Finset.card_le_card at hunion
        rw [Finset.card_union_of_disjoint] at hunion
        · simp [hcard1] at hunion
          calc
            part₁.card = part₁.card * 2 / 2 := by rw [Nat.mul_div_cancel]; trivial
            _ = (part₁.card + part₁.card) / 2 := by ring_nf
            _ ≤ (d - 1) / 2 := by exact Nat.div_le_div_right hunion
        · exact hdisj
      -- if d is even, red.card ≤ d / 2 + 1
      have hred_even : red ⊆ part₁ ∪ {d, d / 2} := by
        intro x hx
        simp [part₁]
        have : x ≤ d := by exact d_max x hx
        rcases lt_or_eq_of_le this with h | h
        · apply Or.inr
          by_cases hxd : x = d / 2
          · apply Or.inr hxd
          · apply Or.inl
            split_ands
            · exact hx
            · exact Nat.ne_of_lt h
            · by_contra heq
              have : x = d / 2 := by
                rw [<-heq, Nat.mul_div_cancel_left]
                exact Nat.zero_lt_two
              contradiction
        · apply Or.inl
          exact h
      have hcard_even : red.card ≤ part₁.card + 2 := by
        apply Finset.card_le_card at hred_even
        have : (part₁ ∪ {d, d / 2}).card ≤ part₁.card + ({d, d / 2} : Finset ℕ).card := by
          apply Finset.card_union_le part₁ {d, d / 2}
        apply Nat.le_trans hred_even at this
        have h : ({d, d / 2} : Finset ℕ).card ≤ 2 := by exact Finset.card_le_two
        exact le_add_of_le_add_left this h
      -- if d is odd, then red.card ≤ (d + 1) / 2
      have hred_odd (hodd : ¬ 2 ∣ d) : red ⊆ part₁ ∪ {d} := by
        intro x hx
        simp [part₁]
        have : x ≤ d := by exact d_max x hx
        rcases lt_or_eq_of_le this with h | h
        · apply Or.inl
          split_ands
          · exact hx
          · exact Nat.ne_of_lt h
          · by_contra h
            have : 2 ∣ d := by use x; simp [h]
            contradiction
        · exact Or.inr h
      have hcard_odd (hodd : ¬ 2 ∣ d) : red.card ≤ part₁.card + 1 := by
        obtain h := hred_odd hodd
        apply Finset.card_le_card at h
        obtain h' := Finset.card_union_le part₁ ({d} : Finset ℕ)
        apply Nat.le_trans h at h'
        simp at h'
        exact h'
      -- claim that d = 2n
      suffices hd : d = 2 * n
      · have hcard₁ : part₁.card ≤ n - 1 := by
          calc
            part₁.card ≤ (d - 1) / 2 := by exact hcard₁
            _ = n - 1 := by
              rw [hd]
              refine mul_sub_div 0 2 n ?_
              calc
                0 < 2 * 2 := by simp
                _ ≤  2 * n := by rel [hn]
        have hdouble : ({2 * n, n} : Finset ℕ).card = 2 := by
          refine Finset.card_pair ?_
          by_contra h
          have : n = 0 := by
            calc
              n = 2 * n - n := by rw [show 2 = 1 + 1 by simp, add_mul, one_mul]; simp
              _ = 0 := by rw [h]; simp
          linarith
        have hred_even : red = part₁ ∪ {2 * n, n} := by
          apply Finset.eq_of_subset_of_card_le
          · rw [hd] at hred_even
            rw [Nat.mul_div_cancel_left] at hred_even
            exact hred_even
            trivial
          · have h := by apply Finset.card_union_le part₁ ({2 * n, n} : Finset ℕ)
            apply Nat.le_trans h
            rw [hdouble, hcard]
            calc
              part₁.card + 2 ≤ n - 1 + 2 := by rel [hcard₁]
              _ = n + 1 := by
                rw [show 2 = 1 + 1 by simp, <-Nat.add_assoc, Nat.sub_add_cancel]
                exact one_le_of_lt hn
        have n_in : n ∈ red := by
          rw [hred_even]
          simp
        -- prove part₁.card = n - 1
        have hcard₁ : part₁.card = n - 1 := by
          apply Nat.le_antisymm
          · exact hcard₁
          · have : red \ {2 * n, n} = part₁ := by
              rw [hred_even]
              refine Finset.union_sdiff_cancel_right ?_
              refine Finset.disjoint_left.mpr ?_
              intro x hx
              simp [part₁, hd] at hx
              simp
              constructor
              · exact hx.right.left
              · exact hx.right.right
            rw [<-this]
            rw [Finset.card_sdiff, hcard, hdouble]
            · simp
            · intro x hx
              simp at hx
              rcases hx with h | h
              · rw [h, <-hd]
                exact d_in
              · rw [h]
                exact n_in
        -- prove n + x ∈ part₁ ∪ part₂
        have hunion : part₁ ∪ part₂ = (Finset.Icc 1 (2 * n - 1)).erase n := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            have h := hx
            simp [part₁, part₂] at h
            have : x ≠ n := by
              rcases h with h | h
              · rw [hd] at h
                simp at h
                exact h.right.right
              · obtain ⟨a, ⟨ha, hfa⟩⟩ := h
                simp [f] at hfa
                simp [hd] at ha hfa
                rw [<-hfa]
                by_contra heq
                have : a = n := by
                  calc
                    a = 2 * n - n := by
                      nth_rw 2 [<-heq]; rw [Nat.sub_sub_self]
                      obtain ha := ha.left
                      apply hsub at ha
                      simp at ha
                      exact ha.right
                    _ = n := by rw [show 2 = 1 + 1 by simp, add_mul, one_mul]; simp
                simp [this] at ha
            apply hunion at hx
            simp at hx ⊢
            constructor
            · exact this
            · rw [hd] at hx
              exact hx
          · suffices : ((Finset.Icc 1 (2 * n - 1)).erase n).card = (part₁ ∪ part₂).card
            · exact Nat.le_of_eq this
            · rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard₁]
              have : n ∈ Finset.Icc 1 (2 * n - 1) := by
                simp
                constructor
                · exact one_le_of_lt hn
                · calc
                    n ≤ 2 * n - n := by rw [show 2 = 1 + 1 by simp, add_mul, one_mul]; simp
                    _ ≤ 2 * n - 1 := by rel [one_le_of_lt hn]
              have h := Finset.card_erase_add_one this
              simp at h
              have : ((Finset.Icc 1 (2 * n - 1)).erase n).card = 2 * n - 1 - 1 := by
                exact Nat.eq_sub_of_add_eq h
              rw [this]
              rw [show 2 = 1 + 1 by simp, add_mul, one_mul, <-Nat.add_sub_assoc]
              congr
              rw [Nat.sub_add_comm]
              · exact one_le_of_lt hn
              · exact one_le_of_lt hn
        -- prove n + x ∉ red
        have x_plus_n_not_in (a : ℕ) (hin : a ∈ red) (hlt : a < n) : n + a ∉ red := by
          by_contra hin'
          have h := hneq a hin n n_in (n + a) hin'
          rw [add_comm] at h
          simp at h
          have : a ≠ n := by exact Nat.ne_of_lt hlt
          apply h at this
          apply hsub at hin
          simp at hin
          obtain hin := hin.left
          have hin : ¬ a = 0 := by exact not_eq_zero_of_lt hin
          apply this at hin
          simp [hin] at hn
        have n_plus_not_in (a : ℕ) (h : a ∈ red) (h' : a < n) : n - a ∈ part₁ := by
          have : n + a ∈ (Finset.Icc 1 (2 * n - 1)).erase n := by
            simp
            split_ands
            · apply hsub at h
              simp at h
              refine Nat.ne_zero_iff_zero_lt.mpr ?_
              exact h.left
            · apply hsub at n_in
              simp at n_in
              have h := n_in.left
              exact le_add_right_of_le h
            · apply hsub at n_in
              simp at n_in
              calc
                n + a ≤ n + (n - 1) := by rel [show a ≤ n - 1 by exact le_sub_one_of_lt h']
                _ = 2 * n - 1 := by rw [<-Nat.add_sub_assoc, show 2 = 1 + 1 by simp, add_mul, one_mul]; exact n_in.left
          rw [<-hunion] at this
          have hnotin : n + a ∉ part₁ := by
            simp [part₁]
            exact fun a_1 _ ↦ False.elim (x_plus_n_not_in a h h' a_1)
          simp at this
          rcases this with h | h
          · contradiction
          · simp [part₂] at h
            obtain ⟨x, ⟨hx, hfx⟩⟩ := h
            simp [f, hd] at hfx
            have : x = n - a := by
              calc
                x = 2 * n - (n + a) := by
                  rw [<-hfx, Nat.sub_sub_self]
                  simp [part₁] at hx
                  obtain h := hx.left
                  apply hsub at h
                  simp at h
                  exact h.right
                _ = n + n - (n + a) := by ring_nf
                _ = n + n - n - a := by rw [Nat.sub_add_eq]
                _ = n - a := by rw [Nat.add_sub_cancel]
            rw [<-this]
            exact hx
        let a := n - x
        have ha : a ∈ part₁ := by simp [a]; exact n_plus_not_in x hin hlt
        simp [part₁, hd] at ha
        obtain h := hneq x hin a ha.left n n_in
        have : x + a = n := by simp [a]; rw [Nat.add_sub_cancel']; exact le_of_succ_le hlt
        simp [this] at h
        simp [ha.right.right] at h
        by_cases hxa : ¬ x = a
        · apply h at hxa
          simp [hxa] at hlt
        · simp at hxa
          rw [hxa] at this
          by_cases h' : 2 * a - 1 ∈ red
          · have h1in : 1 ∈ part₁ := by
              obtain ha := ha.left
              apply hsub at ha
              simp at ha
              have hlt : 2 * a - 1 < n := by
                simp [<-this]
                calc
                  2 * a - 1 < 2 * a := by
                    apply Nat.sub_lt_self; trivial
                    calc
                      1 ≤ 2 * 1 := by simp
                      _ ≤ 2 * a := by rel [ha.left]
                  _ = a + a := by ring
              apply n_plus_not_in (2 * a - 1) h' at hlt
              rw [<-this] at hlt
              have : a + a - (2 * a - 1) = 1 := by
                rw [show a + a = 2 * a by ring]
                rw [Nat.sub_sub_self]
                calc
                  1 ≤ 2 * 1 := by simp
                  _ ≤ 2 * a := by rel [ha.left]
              rw [<-this]
              exact hlt
            simp [part₁] at h1in
            obtain h := h1in.left
            rw [<-this] at n_in
            have hgt : a + a ≥ 1 := by
              obtain h := ha.left
              apply hsub at h
              simp at h
              calc
                a + a ≥ 1 + 1 := by rel [h.left]
                _ ≥ 1 := by simp
            obtain h' := hneq 1 h (2 * a - 1) h' (a + a) n_in
            rw [Nat.add_sub_cancel'] at h'
            simp [show 2 * a = a + a by ring] at h'
            rw [hd] at h1in
            obtain h := h1in.right.right
            have hn1 : ¬ 1 = n := by
              by_contra heq
              simp [<-heq] at h
            rw [<-this] at hn1
            simp [hn1] at h'
            have h : a + a - 1 ≠ a + a := by
              have : a + a - 1 < a + a := by exact sub_one_lt_of_lt hgt
              exact Nat.ne_of_lt this
            simp [h] at h'
            have h : a + a = 1 + 1 := by nth_rw 1 [h']; rw [Nat.sub_add_cancel hgt]
            rw [h] at this
            simp [<-this] at hn
            simp_arith at hgt
            exact hgt
          · suffices hin : 2 * a + 1 ∈ red
            · have hnin' : 3 * a + 1 ∉ red := by
                by_contra hin'
                have h := hneq (2 * a + 1) hin a ha.left (3 * a + 1) hin'
                rw [add_comm] at h
                simp at h
                have : 1 + 2 * a + a = 3 * a + 1 := by simp_arith
                simp [this] at h
                have : ¬ 1 + 2 * a = 3 * a + 1 := by
                  by_contra heq
                  have : a = 0 := by
                    calc
                      a = (3 * a + 1) - (2 * a + 1) := by
                        rw [<-Nat.sub_sub]; rw [Nat.sub_add_comm]
                        rw [Nat.add_sub_cancel]
                        rw [<-Nat.sub_mul]
                        simp
                        rel [show 2 ≤ 3 by simp]
                      _ = (1 + 2 * a) - (2 * a + 1) := by rw [<-heq]
                      _ = 0 := by rw [add_comm]; simp
                  obtain h := ha.left
                  apply hsub at h
                  simp [this] at h
                simp [this] at h
                have : ¬ 1 + 2 * a = a := by
                  have : 1 + 2 * a > a := by
                    calc
                      1 + 2 * a > 2 * a := by exact lt_one_add (2 * a)
                      _ ≥ 1 * a := by rel [show 2 > 1 by simp]
                      _ = a := by simp
                  exact Nat.ne_of_lt' this
                simp [this] at h
                have : ¬ a = 3 * a + 1 := by
                  have : 3 * a + 1 > a := by
                    calc
                      3 * a + 1 > 3 * a := by exact lt_add_one (3 * a)
                      _ ≥ 1 * a := by rel [show 3 > 1 by simp]
                      _ = a := by simp
                  exact Nat.ne_of_lt this
                simp [this] at h
              have hin' : a - 1 ∈ red := by
                have : 3 * a + 1 ∈ part₁ ∪ part₂ := by
                  rw [hunion]
                  simp
                  constructor
                  · have : 3 * a + 1 > n := by
                      rw [<-this]
                      calc
                        3 * a + 1 > 3 * a := by apply Nat.lt_add_one
                        _ ≥ 2 * a := by rel [show 3 ≥ 2 by simp]
                        _ = a + a := by ring
                    exact Nat.ne_of_gt this
                  · rw [<-this]
                    have : a ≥ 2 := by
                      by_contra hlt
                      push_neg at hlt
                      rw [<-this] at hn
                      revert hn
                      interval_cases a
                      all_goals decide
                    calc
                      3 * a + 1 = 3 * a + 2 - 1 := by rw [Nat.add_sub_assoc]; trivial
                      _ ≤ 3 * a + a - 1 := by rel [this]
                      _ = 2 * (a + a) - 1 := by congr; ring
                simp at this
                rcases this with h | h
                · simp [part₁] at h
                  obtain h := h.left
                  contradiction
                · simp [part₂] at h
                  obtain ⟨a', ⟨ha', hfa'⟩⟩ := h
                  simp [f, hd, <-this] at hfa'
                  have : a' = a - 1 := by
                    calc
                      a' = 2 * (a + a) - (3 * a + 1) := by
                        rw [<-hfa', Nat.sub_sub_self]
                        rw [this]
                        simp [part₁, hd] at ha'
                        have h := ha'.left
                        apply hsub at h
                        simp at h
                        exact h.right
                      _ = 4 * a - 3 * a - 1 := by rw [Nat.sub_sub]; congr 1; ring
                      _ = a - 1 := by rw [<-Nat.sub_mul]; simp
                  rw [<-this]
                  simp [part₁] at ha'
                  exact ha'.left
              have hlt : a - 1 < n := by
                rw [<-this]
                calc
                  a - 1 < a := by
                    apply Nat.sub_one_lt
                    obtain h := ha.left
                    apply hsub at h
                    simp at h
                    by_contra heq
                    simp [heq] at h
                  _ ≤ a + a := by exact Nat.le_add_right a a
              obtain h := n_plus_not_in (a - 1) hin' hlt
              simp [<-this, part₁] at h
              obtain h := h.left
              apply hneq a ha.left (a + a - (a - 1)) h (2 * a + 1) at hin
              simp at hin
              have hapos : a ≥ 1 := by
                obtain h := ha.left
                apply hsub at h
                simp at h
                exact h.left
              have : a + (a + a - (a - 1)) = 2 * a + 1 := by
                rw [Nat.add_sub_assoc, Nat.sub_sub_self, <-Nat.add_assoc]
                ring
                exact hapos
                exact sub_le_succ_sub a 1
              simp [this] at hin
              have : ¬ a = 2 * a + 1 := by
                have : a < 2 * a + 1 := by
                  calc
                    a ≤ 2 * a := by nth_rw 1 [<-one_mul a]; rel [show 1 ≤ 2 by simp]
                    _ < 2 * a + 1 := by exact Nat.lt_add_one (2 * a)
                apply Nat.ne_of_lt this
              simp [this] at hin
              have :  ¬ a + a - (a - 1) = 2 * a + 1 := by
                rw [Nat.add_sub_assoc, Nat.sub_sub_self]
                · apply Nat.ne_of_lt
                  calc
                    a + 1 ≤ a + a := by rel[hapos]
                    _ = 2 * a := by ring
                    _ < 2 * a + 1 := by apply Nat.lt_add_one
                · exact hapos
                · exact sub_le_succ_sub a 1
              simp [this] at hin
              have : ¬ a = a + a - (a - 1) := by
                have : a < a + a - (a - 1) := by
                  calc
                    a < a + 1 := by apply Nat.lt_add_one
                    _ = a + a - (a - 1) := by
                      rw [Nat.add_sub_assoc]
                      rw [Nat.sub_sub_self]
                      exact hapos
                      exact sub_le_succ_sub a 1
                apply Nat.ne_of_lt this
              contradiction
            · have hin : 2 * a + 1 ∈ part₁ ∪ part₂ := by
                rw [hunion, <-this]
                simp
                constructor
                · have : 2 * a + 1 > a + a := by
                    calc
                      2 * a + 1 > 2 * a := by apply Nat.lt_add_one
                      _ = a + a := by ring
                  apply Nat.ne_of_gt this
                · rw [show 2 * a = a + a by ring, this]
                  calc
                    n + 1 = n + 2 - 1 := by rw [Nat.add_sub_assoc]; trivial
                    _ ≤ n + n - 1 := by rel [show 2 ≤ n by exact le_of_succ_le hn]
                    _ = 2 * n - 1 := by ring_nf
              simp at hin
              rcases hin with h | h
              · simp [part₁] at h
                exact h.left
              · simp [part₂, f] at h
                obtain ⟨x, ⟨hx, hfx⟩⟩ := h
                simp [hd, <-this] at hfx
                have : x = 2 * a - 1 := by
                  calc
                    x = 2 * (a + a) - (2 * a + 1) := by
                      rw [<-hfx, Nat.sub_sub_self]
                      rw [this]
                      simp [part₁] at hx
                      obtain h := hx.left
                      apply hsub at h
                      simp at h
                      exact h.right
                    _ = 4 * a - 2 * a - 1 := by rw [Nat.sub_sub]; congr 1; ring
                    _ = 2 * a - 1 := by rw [<-Nat.sub_mul]
                rw [<-this] at h'
                simp [part₁] at hx
                obtain h := hx.left
                contradiction
      · -- prove the claim
        by_contra hneq
        rcases lt_or_gt_of_ne hneq with hlt | hgt
        · have : d ≤ 2 * n - 1 := by exact le_sub_one_of_lt hlt
          have : red.card ≤ n := by
            by_cases heven : 2 ∣ d
            · -- if 2 ∣ n, red.card ≤ n, contradiction
              have hneq : d ≠ 2 * n - 1 := by
                by_contra heq
                rw [heq] at heven
                obtain ⟨k, hk⟩ := heven
                have : 2 ∣ 1 := by
                  use n - k
                  rw [Nat.mul_sub, <-hk, Nat.sub_sub_self]
                  calc
                    1 ≤ 2 * 2 := by simp
                    _ ≤ 2 * n := by rel [hn]
                simp at this
              have : d ≤  2 * n - 1 - 1 := by
                refine (Nat.le_sub_one_iff_lt ?_).mpr ?_
                · calc
                    0 < 2 * 2 - 1 := by simp
                    _ ≤ 2 * n - 1 := by rel [hn]
                · exact Nat.lt_of_le_of_ne this hneq
              calc
                red.card ≤ part₁.card + 2 := by rel [hcard_even]
                _ ≤ (d - 1) / 2 + 2 := by rel [hcard₁]
                _ ≤ (2 * n - 1 - 1 - 1) / 2 + 2 := by rel [this]
                _ = (2 * n - 3) / 2 + 2 := by rw [show 3 = 1 + 1 + 1 by simp, Nat.sub_add_eq, Nat.sub_add_eq]
                _ = n - 2 + 2 := by
                  congr
                  refine mul_sub_div 2 2 n ?_
                  calc
                    2 < 2 * 2 := by simp
                    _ ≤ 2 * n := by rel[hn]
                _ = n := by rw [Nat.sub_add_cancel]; exact le_of_succ_le hn
            · -- if ¬ 2 ∣ n, red.card ≤ n, contradiction
              calc
                red.card ≤ part₁.card + 1 := by rel [hcard_odd heven]
                _ ≤ (d - 1) / 2 + 1 := by rel [hcard₁]
                _ ≤ (2 * n - 1 - 1) / 2 + 1 := by rel [this]
                _ = n - 1 + 1 := by
                  congr
                  refine Nat.div_eq_of_eq_mul_right ?_ ?_
                  · trivial
                  · rw [Nat.mul_sub, mul_one, show (2 = 1 + 1) by simp, Nat.sub_add_eq]
                _ = n := by rw [Nat.sub_add_cancel]; exact one_le_of_lt hn
          simp [hcard] at this
        · -- d > 2 * n, impossible
          apply hsub at d_in
          simp at d_in
          have : ¬ d > 2 * n := by push_neg; exact d_in.right
          contradiction
