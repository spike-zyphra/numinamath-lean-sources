import Mathlib

open Finset

set_option maxHeartbeats 0 in
/- Let $X$ be a set of 10000 integers, none of them is divisible by 47 . Prove that there exists a 2007-element subset $Y$ of $X$ such that $a-b+c-d+e$ is not divisible by 47 for any $a, b, c, d, e \in Y$.  (Netherlands) -/
theorem combinatorics_23700 (X : Finset ℤ) (hX : X.card = 10000)
    (hX1 : ∀ x ∈ X, ¬ 47 ∣ x) :
    ∃ Y ⊆ X, Y.card = 2007 ∧ ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ∀ d ∈ Y, ∀ e ∈ Y,
    ¬ 47 ∣ a - b + c - d + e := by
  have _ : Fact (Nat.Prime 47) := by
    decide
  -- Call a set $M$ of integers good if $47 \nmid a-b+c-d+e$ for any $a, b, c, d, e \in M$.
  let Good (M : Finset ℤ) := ∀ a ∈ M, ∀ b ∈ M, ∀ c ∈ M, ∀ d ∈ M, ∀ e ∈ M, ¬ 47 ∣ a - b + c - d + e
  -- Consider the set $J=\{-9,-7,-5,-3,-1,1,3,5,7,9\}$.
  let J : Finset ℤ := {-9, -7, -5, -3, -1, 1, 3, 5, 7, 9}
  -- We claim that $J$ is good.
  have h1 : Good J := by
    -- Actually, for any $a, b, c, d, e \in J$ the number $a-b+c-d+e$ is odd
    intro a ha b hb c hc d hd e he
    have h2 : Odd (a - b + c - d + e) := by
      have hJ_odd : ∀ j ∈ J, Odd j := by
        decide
      have ha_odd : Odd a := hJ_odd a ha
      have hb_odd : Odd b := hJ_odd b hb
      have hc_odd : Odd c := hJ_odd c hc
      have hd_odd : Odd d := hJ_odd d hd
      have he_odd : Odd e := hJ_odd e he
      simp [Int.odd_add', Int.even_sub', ha_odd, hb_odd, hc_odd, hd_odd, he_odd]
    -- and $$ -45=(-9)-9+(-9)-9+(-9) \leq a-b+c-d+e \leq 9-(-9)+9-(-9)+9=45 $$
    have h3 : -45 ≤ a - b + c - d + e ∧ a - b + c - d + e ≤ 45 := by
      have this : ∀ j ∈ J, -9 ≤ j ∧ j ≤ 9 := by
        decide
      have ha_ge := this a ha
      have hb_ge := this b hb
      have hc_ge := this c hc
      have hd_ge := this d hd
      have he_ge := this e he
      omega
    -- But there is no odd number divisible by 47 between -45 and 45.
    obtain ⟨h3, h4⟩ := h3
    interval_cases a - b + c - d + e
    all_goals norm_num
    simp at h2
  -- For any $k=1, \ldots, 46$ consider the set $$ A_{k}=\{x \in X \mid \exists j \in J: \quad k x \equiv j(\bmod 47)\} . $$
  let A (k : ℤ) : Finset ℤ := {x ∈ X | ∃ j ∈ J, k * x ≡ j [ZMOD 47]}
  have h2 : ∀ k, Good (A k) := by
    intro k
    -- If $A_{k}$ is not good, then $47 \mid a-b+c-d+e$ for some $a, b, c, d, e \in A_{k}$,
    by_contra h
    simp [Good] at h
    obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, h⟩ := h
    -- hence $47 \mid k a-k b+ k c-k d+k e$.
    have h' : 47 ∣ k * a - k * b + k * c - k * d + k * e := by
      have : k * a - k * b + k * c - k * d + k * e = k * (a - b + c - d + e) := by ring
      rw [this]
      exact h.mul_left k
    -- But set $J$ contains numbers with the same residues modulo 47, so $J$ also is not good
    simp [A] at ha hb hc hd he
    obtain ⟨_, ja, hja1, hja2⟩ := ha
    obtain ⟨_, jb, hjb1, hjb2⟩ := hb
    obtain ⟨_, jc, hjc1, hjc2⟩ := hc
    obtain ⟨_, jd, hjd1, hjd2⟩ := hd
    obtain ⟨_, je, hje1, hje2⟩ := he
    specialize h1 _ hja1 _ hjb1 _ hjc1 _ hjd1 _ hje1
    rw [show (47 : ℤ) = (47 : ℕ) by simp] at h' h1 hja2 hjb2 hjc2 hjd2 hje2
    rw [← ZMod.intCast_eq_intCast_iff] at hja2 hjb2 hjc2 hjd2 hje2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at h' h1
    simp at h' h1 hja2 hjb2 hjc2 hjd2 hje2
    rw [hja2, hjb2, hjc2, hjd2, hje2] at h'
    -- This is a contradiction; therefore each $A_{k}$ is a good subset of $X$.
    contradiction
  -- Then it suffices to prove that there exists a number $k$ such that $\left|A_{k}\right| \geq 2007$.
  suffices ∃ k, (A k).card ≥ 2007 by
    obtain ⟨k, hk⟩ := this
    obtain ⟨Y, hY1, hY2⟩ := Finset.exists_subset_card_eq hk
    use Y
    constructor
    · trans A k
      · exact hY1
      · simp [A]
    constructor
    · exact hY2
    intro a ha b hb c hc d hd e he
    apply hY1 at ha
    apply hY1 at hb
    apply hY1 at hc
    apply hY1 at hd
    apply hY1 at he
    exact h2 _ _ ha _ hb _ hc _ hd _ he
  -- Note that each $x \in X$ is contained in exactly 10 sets $A_{k}$.
  have h3 : ∀ x ∈ X, #((Finset.Icc 1 46).filter (fun k ↦ x ∈ A k)) = 10 := by
    intro x hx
    let f : ℤ → ℤ := fun j ↦ ((j : ZMod 47) / (x : ZMod 47) : ZMod 47).val
    have : ((Finset.Icc 1 46).filter (fun k ↦ x ∈ A k)) = J.image f := by
      ext k
      simp
      constructor
      · intro ⟨⟨hk1, hk2⟩, hx⟩
        simp [f]
        simp [A] at hx
        obtain ⟨hx, j, hj1, hj2⟩ := hx
        use j, hj1
        rw [show (47 : ℤ) = (47 : ℕ) by simp, ← ZMod.intCast_eq_intCast_iff] at hj2
        simp at hj2
        rw [← hj2]
        rw [mul_div_cancel_right₀]
        · rw [ZMod.coe_intCast]
          simp
          apply Int.emod_eq_of_lt <;> omega
        simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
        solve_by_elim
      · intro ⟨j, hj1, hj2⟩
        constructor
        · simp [f] at hj2
          rw [← hj2]
          set a := ((j : ZMod 47) / (x : ZMod 47) : ZMod 47)
          constructor
          · suffices a ≠ 0 by
              rw [ZMod.cast_eq_val]
              suffices a.val ≠ 0 by omega
              exact (ZMod.val_ne_zero a).mpr this
            simp [a, -ne_eq]
            apply div_ne_zero
            · simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
              have : ∀ j ∈ J, ¬ (47 ∣ j) := by
                decide
              solve_by_elim
            · simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
              solve_by_elim
          · rw [ZMod.cast_eq_val]
            suffices a.val < 47 by omega
            apply ZMod.val_lt
        · simp [f] at hj2
          simp [A, hx]
          use j, hj1
          rw [← hj2]
          rw [show (47 : ℤ) = (47 : ℕ) by simp, ← ZMod.intCast_eq_intCast_iff]
          simp
          rw [div_mul_cancel₀]
          simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
          solve_by_elim
    rw [this]
    apply Finset.card_image_of_injOn
    intro j1 hj1 j2 hj2 h
    simp [f] at h
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, Int.ofNat_inj] at h
    apply ZMod.val_injective at h
    rw [div_left_inj'] at h
    swap
    · simp [ZMod.intCast_zmod_eq_zero_iff_dvd]
      solve_by_elim
    have : ∀ j1 ∈ J, ∀ j2 ∈ J, (j1 : ZMod 47) = (j2 : ZMod 47) → j1 = j2 := by
      clear * - J
      decide +revert
    solve_by_elim
  -- Then $$ \sum_{k=1}^{46}\left|A_{k}\right|=10|X|=100000 $$
  have h4 : ∑ k in Finset.Icc 1 46, (A k).card = 100000 := by
    calc
      _ = #X * 10 := by
        conv => lhs; arg 2; ext k; rw [Finset.card_eq_sum_ones]
        rw [Finset.sum_comm' (t' := X) (s' := fun x ↦ (Icc (1 : ℤ) 46).filter (fun k ↦ x ∈ A k))]
        · simp_rw [← Finset.card_eq_sum_ones]
          rwa [Finset.sum_const_nat]
        intro k x
        constructor
        · intro ⟨hk, hx⟩
          constructor
          · simp [hk, hx]
          · simp [A] at hx
            tauto
        · intro ⟨hk, hx⟩
          constructor
          · simp at hk ⊢
            tauto
          · simp at hk
            tauto
      _ = 100000 := by
        simp [hX]
  -- hence for some value of $k$ we have $$ \left|A_{k}\right| \geq \frac{100000}{46}>2173>2007 . $$
  have h5 : ∃ k, (A k).card ≥ 2173 := by
    by_contra! h
    have := Finset.sum_le_card_nsmul (Icc 1 46) (fun k ↦ (A k).card) 2173
      (by intro x _; specialize h x; simp; omega)
    simp at this
    omega
  -- This completes the proof.
  obtain ⟨k, hk⟩ := h5
  use k
  omega
