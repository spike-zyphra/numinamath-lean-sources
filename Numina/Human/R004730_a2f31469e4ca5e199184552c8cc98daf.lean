import Mathlib

/- A theorem in newer version of Mathlib, allowing to rewrite
  a ≡ c [MOD b] to ∃ k, a = b * k + c -/
lemma mod_eq_iff {a b c : Nat} :
    a % b = c ↔ (b = 0 ∧ a = c) ∨ (c < b ∧ Exists fun k => a = b * k + c) :=
  ⟨fun h =>
    if w : b = 0 then
      .inl ⟨w, by simpa [w] using h⟩
    else
      .inr ⟨by subst h; exact Nat.mod_lt a (Nat.zero_lt_of_ne_zero w),
        a / b, by subst h; exact (Nat.div_add_mod a b).symm⟩,
    by
      rintro (⟨rfl, rfl⟩ | ⟨w, h, rfl⟩)
      · simp_all
      · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt w]⟩

/-Three, (25 points) In the set of numbers $1,2, \cdots, 2009$, what is the maximum number of numbers that can be selected such that the sum of any two selected numbers is divisible by 100?-/
theorem number_theory_311999 : IsGreatest {Finset.card S | (S : Finset ℕ) (_ : S ⊆ Finset.Icc 1 2009 ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 100 ∣ x + y)} 20 := by

  constructor
  · -- the set S = {100, 200, ..., 2000} shows that 20 such numbers can be selected
    let f : ℕ → ℕ := fun i ↦ 100 * i
    have : Function.Injective f := by
      unfold f
      refine mul_right_injective₀ ?_
      norm_num

    let f_emb : Function.Embedding ℕ ℕ := by
      refine {toFun := f, inj' := this}

    let S := (Finset.Icc 1 20).map f_emb
    use S; simp
    constructor; constructor
    · intro x hx
      simp [S, f_emb, f] at hx
      obtain ⟨a, ⟨⟨ha1, ha2⟩, hax⟩⟩ := hx
      simp
      constructor <;> linarith
    · intro x hx y hy hne
      simp [S, f_emb, f] at hx hy
      obtain ⟨a, ⟨_, hax⟩⟩ := hx
      obtain ⟨b, ⟨_, hby⟩⟩ := hy
      rw [← hax, ← hby]
      rw [show 100 * a + 100 * b = 100 * (a + b) by ring]
      simp only [dvd_mul_right]
    · simp only [Finset.card_map, Nat.card_Icc, Nat.reduceAdd, Nat.add_one_sub_one, S]

  · -- on the other hand, for any such set S of selected numbers, we show that S conains at most 20 elements.

    intro x xmem
    simp at xmem
    obtain ⟨S, ⟨hS_subset, hS_dvd⟩, rfl⟩ := xmem

    by_cases h_S_three : S.card < 3
    · -- first we handle the trivial case that |S| < 3
      linarith only [h_S_three]
    · -- so in the following we can assume that |S| > 3
      push_neg at h_S_three

      -- we prove that numbers in S are multiples of 50.
      have h_50_dvd_of_mem_S : ∀ a ∈ S, 50 ∣ a := by
        -- take any 3 numbers a, b, c ∈ S
        intro a amem
        let S' := S \ {a}
        have : S'.card = S.card - 1 := by
          simp [S']
          rw [show 1 = ({a} : Finset ℕ).card by rfl]
          refine Finset.card_sdiff ?_
          simp only [Finset.singleton_subset_iff, amem]
        have : S'.card > 1 := by rw [this]; exact Nat.lt_sub_of_add_lt h_S_three
        have ⟨b, bmem, c, cmem, hne⟩ := Finset.one_lt_card.mp this
        have h_ba : b ≠ a := by
          intro heq
          rw [heq] at bmem
          simp [S'] at bmem
        have h_ca : c ≠ a := by
          intro heq
          rw [heq] at cmem
          simp [S'] at cmem
        have bmemS : b ∈ S := by
          simp [S'] at bmem
          exact bmem.1
        have cmemS : c ∈ S := by
          simp [S'] at cmem
          exact cmem.1

        -- then (1) a + b = 100 * k1
        have h1 := hS_dvd a amem b bmemS h_ba.symm
        have h1' : (100 : ℤ) ∣ a + b := by
          exact Int.natAbs_dvd_natAbs.mp h1
        have ⟨k1, hk1⟩ := h1'

        -- (2) a + c = 100 * k2
        have h2 := hS_dvd a amem c cmemS h_ca.symm
        have h2' : (100 : ℤ) ∣ a + c := by
          exact Int.natAbs_dvd_natAbs.mp h2
        have ⟨k2, hk2⟩ := h2'

        -- (3) b + c = 100 * k3
        have h3 := hS_dvd b bmemS c cmemS hne
        have h3' : (100 : ℤ) ∣ b + c := by
          exact Int.natAbs_dvd_natAbs.mp h3
        have ⟨k3, hk3⟩ := h3'

        -- (1) + (2) - (3) gives a = 50 * (k1 + k2 - k3)
        have ha_eq : a = 50 * (k1 + k2 - k3) := by
          suffices h : 2 * a = 100 * (k1 + k2 - k3) by
            linarith only [h]
          linear_combination2 hk1 + hk2 - hk3

        -- therefore 50 ∣ a
        have : (50 : ℤ) ∣ a := by exact Dvd.intro (k1 + k2 - k3) ha_eq.symm
        norm_cast at this

      -- However, the multiples can only be all odd or all even to be divisible by 100
      have : (∀ a ∈ S, a ≡ 50 [MOD 100]) ∨ (∀ a ∈ S, a ≡ 0 [MOD 100]) := by
        by_cases h_50 : ∀ a ∈ S, a ≡ 50 [MOD 100]
        · left; assumption

        push_neg at h_50
        right

        obtain ⟨a, amem, ha⟩ := h_50
        have ⟨k, hk⟩ := h_50_dvd_of_mem_S a amem

        have ⟨t, ht⟩ : Even k := by
          by_contra h
          have ⟨t, ht⟩ : Odd k := by exact Nat.not_even_iff_odd.mp h
          rw [ht, show 50 * (2 * t + 1) = 100 * t + 50 by ring] at hk
          have : a ≡ 50 [MOD 100] := by
            refine Nat.modEq_of_dvd ?_
            rw [hk]
            simp
          exact ha this

        have h_a_modeq_0 : a ≡ 0 [MOD 100] := by
          rw [hk, ht, ← two_mul, ← mul_assoc]
          norm_num
          refine Nat.modEq_zero_iff_dvd.mpr ?_
          exact Nat.dvd_mul_right 100 t

        by_contra! h
        obtain ⟨b, bmem, hb⟩ := h

        have h1 : a + b ≡ 0 [MOD 100] := by
          refine Nat.ModEq.symm (Dvd.dvd.zero_modEq_nat ?_)
          apply hS_dvd a amem b bmem
          intro heq
          rw [← heq] at hb
          contradiction

        have h2 : b ≡ 0 [MOD 100] := by
          trans a + b
          nth_rw 1 [show b = 0 + b by ring]
          gcongr
          exact h1

        contradiction

      -- so the numbers that meet the conditions are
      -- 50, 150, ..., 1950 or
      -- 100, 200, ..., 2000,
      -- with 20 numbers in each set.
      rcases this with h_left | h_right
      ·
        let f : ℕ → ℕ := fun i ↦ 100 * i + 50
        have : Function.Injective f := by
          unfold f
          intro x y heq
          simp at heq
          exact heq

        let f_emb : Function.Embedding ℕ ℕ := by
          refine {toFun := f, inj' := this}

        let U := (Finset.Icc 0 19).map f_emb

        have hU_card : U.card = 20 := by simp [U]

        have : S ⊆ U := by
          intro a amem
          have ha_modeq := h_left a amem
          apply mod_eq_iff.mp at ha_modeq
          simp at ha_modeq
          obtain ⟨k, hk⟩ := ha_modeq

          simp [U]
          use k
          constructor
          · by_contra! h
            have : a ≥ 2050 := by linarith only [h, hk]
            have : a ∈ Finset.Icc 1 2009 := by exact hS_subset amem
            simp at this
            linarith
          · simp [f_emb, f, hk]

        have : S.card ≤ U.card := by exact Finset.card_le_card this
        linarith only [this, hU_card]
      ·
        let f : ℕ → ℕ := fun i ↦ 100 * i
        have : Function.Injective f := by
          unfold f
          intro x y heq
          simp at heq
          exact heq

        let f_emb : Function.Embedding ℕ ℕ := by
          refine {toFun := f, inj' := this}

        let U := (Finset.Icc 1 20).map f_emb

        have hU_card : U.card = 20 := by simp [U]

        have : S ⊆ U := by
          intro a amem
          have ha_modeq := h_right a amem
          apply mod_eq_iff.mp at ha_modeq
          simp at ha_modeq
          obtain ⟨k, hk⟩ := ha_modeq

          simp [U]
          use k
          constructor
          · constructor
            · by_contra! h
              have : k = 0 := by exact Nat.lt_one_iff.mp h
              rw [this, mul_zero] at hk
              have : a ∈ Finset.Icc 1 2009 := by exact hS_subset amem
              simp at this
              linarith
            · by_contra! h
              have : a ≥ 2100 := by linarith only [h, hk]
              have : a ∈ Finset.Icc 1 2009 := by exact hS_subset amem
              simp at this
              linarith
          · simp [f_emb, f, hk]

        have : S.card ≤ U.card := by exact Finset.card_le_card this
        linarith only [this, hU_card]
