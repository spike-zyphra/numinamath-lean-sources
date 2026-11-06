import Mathlib

/-
  Consider an odd prime number  $p$  and  $p$  consecutive positive integers  $m_1,m_2,…,m_p$ .
Choose a permutation  $\sigma$  of  $1,2,…,p$  .
Show that there exist two different numbers  $k,l\in{(1,2,…,p)}$  such that  $p\mid{m_k.m_{\sigma(k)}-m_l.m_{\sigma(l)}}$
-/
theorem number_theory_8538 {p : ℕ} (hodd : Odd p) (hp : Nat.Prime p)
    (m : Finset.Icc 1 p → ℕ+) (hm : ∃ m₀, ∀ i : Finset.Icc 1 p, (m i).val = m₀ + i ) (σ : Equiv.Perm (Finset.Icc 1 p)) :
    ∃ k l : Finset.Icc 1 p, k ≠ l ∧ ↑p ∣ (m k : ℤ) * m (σ k) - m l * m (σ l) := by

  have hp' : Fact (Nat.Prime p) := by exact { out := hp }

  -- x % p ∈ [0, p-1]
  have in_finset (x : ℕ) : x % p ∈ Finset.range p := by
    simp
    refine Nat.mod_lt x ?_
    exact Nat.Prime.pos hp

  -- if |x - y | < p, then x % p=y%p → x=y
  have eq_of_mod (p x y : ℕ) (h1 : x < y + p) (h2 : y < x + p) (hxy : x % p = y % p) : x = y := by
    obtain ⟨c, hc⟩ : ↑p ∣ x - (y : ℤ) := by exact Nat.modEq_iff_dvd.mp (Eq.symm hxy)
    by_cases h : c = 0
    · simp [h] at hc
      have : x = (y : ℤ) := by exact Int.eq_of_sub_eq_zero hc
      norm_cast at this
    · rcases lt_or_gt_of_ne h with h | h
      · have : -c > 0 := by exact Int.neg_pos_of_neg h
        have : -c ≥ 1 := by linarith [this]
        have : ¬ y < x + (p : ℤ) := by
          push_neg
          calc
            y = x + p * (-c) := by linarith [hc]
            _ ≥ x + p * 1 := by rel [this];
            _ = x + p := by simp
        norm_cast at this
      · have : c ≥ 1 := by exact h
        have : ¬ x < y + (p : ℤ) := by
          push_neg
          calc
            x = y + p * c := by linarith [hc]
            _ ≥ y + p * 1 := by rel [this]
            _ = y + p := by simp
        norm_cast at this

  -- the case for 0 ... p - 1
  have case_for_range_p (σ : Equiv.Perm (Finset.range p)) :
      ∃ k l : Finset.range p, k ≠ l ∧ ↑p ∣ (k : ℤ) * (σ k) - l * (σ l) := by

    -- by contradiction
    by_contra hndvd
    push_neg at hndvd

    -- show that σ has preimage for every y ∈ [0, p-1]
    have preimag_exists (y : Finset.range p) : ∃ x : Finset.range p, σ x = y := by
      obtain ⟨x, hx⟩ := (Equiv.surjective σ) y
      use x

    -- 0 ∈ finset [0, p-1]
    let zero_fin : Finset.range p := ⟨0, in_finset 0⟩

    -- prove σ 0 = 0
    have σ_0_to_0 : σ zero_fin = zero_fin := by
      obtain ⟨x, happ⟩ := preimag_exists zero_fin
      by_cases hp : x = zero_fin
      · rw [hp] at happ
        exact happ
      · push_neg at hp
        apply hndvd x zero_fin at hp
        simp [happ] at hp

    -- def [1, p-1]
    let finset_p_non_zero := {x : Finset.range p | x ≠ zero_fin}

    -- prove ∏ x ∈ [1, p - 1], x * σ x = ∏ x ∈ [1, p - 1], x
    have prod_f : ∏ x ∈ finset_p_non_zero, (x.val * (σ x).val) % p = ∏ x ∈ finset_p_non_zero, x.val := by
      let i (a : Finset.range p) (_ : a ∈ finset_p_non_zero.toFinset) : Finset.range p :=
        let y := (a.val * (σ a).val) % p
        have : y ∈ Finset.range p := by simp [y]; refine Nat.mod_lt (↑a * ↑(σ a)) ?_; exact Nat.Prime.pos hp
        ⟨y, this⟩
      have h1 (a : Finset.range p) (ha : a ∈ finset_p_non_zero.toFinset) : i a ha ∈ finset_p_non_zero.toFinset := by
        simp [i, finset_p_non_zero]
        simp [finset_p_non_zero] at ha
        apply hndvd a zero_fin at ha
        by_contra heq
        simp [zero_fin] at heq ha
        have : p ∣ a.val * (σ a).val := by exact Nat.dvd_of_mod_eq_zero heq
        norm_cast at ha
      have h2 (a₁ : Finset.range p) (ha₁ : a₁ ∈ finset_p_non_zero.toFinset)
          (a₂ : Finset.range p) (ha₂ : a₂ ∈ finset_p_non_zero.toFinset) (h : i a₁ ha₁ = i a₂ ha₂) : a₁ = a₂ := by
        simp [i] at h
        have : (a₁.val : ℤ) * (σ a₁).val % p - a₂.val * (σ a₂).val % p = 0 := by norm_cast; rw[h]; exact Int.subNatNat_self (↑a₂ * ↑(σ a₂) % p)
        have : ((a₁.val : ℤ) * (σ a₁).val - a₂.val * (σ a₂).val) % p = 0 := by rw [Int.sub_emod, this]; trivial
        have : ↑p ∣ (a₁.val : ℤ) * (σ a₁).val - a₂.val * (σ a₂).val := by exact Int.dvd_of_emod_eq_zero this
        by_contra hneq
        apply hndvd a₁ a₂ at hneq
        contradiction
      have h3 (b : Finset.range p) (hb : b ∈ finset_p_non_zero.toFinset) : ∃ a, ∃ (ha : a ∈ finset_p_non_zero.toFinset), i a ha = b := by
        by_contra h
        push_neg at h
        let domain := finset_p_non_zero.toFinset.erase b
        have hi (a : Finset.range p) (ha : a ∈ finset_p_non_zero.toFinset) : i a ha ∈ domain := by
          simp [domain, i]
          constructor
          · exact h a ha
          · apply h1 a at ha; simp at ha; exact ha
        have hcard1 : domain.card + 1 = finset_p_non_zero.toFinset.card := by
          simp only [domain]
          apply Finset.card_erase_add_one
          exact hb
        have hcard : domain.card * 1 < finset_p_non_zero.toFinset.card := by
          rw [<-hcard1]
          simp
        obtain ⟨y, ⟨_, hy2⟩⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hi hcard
        obtain ⟨x1, ⟨x2, ⟨hx1, ⟨hx2, hneq⟩⟩⟩⟩ := Finset.one_lt_card_iff.mp hy2
        simp at hx1 hx2
        have : i x1 (Set.mem_toFinset.mpr hx1.left) = i x2 (Set.mem_toFinset.mpr hx2.left) := by
          apply Eq.trans hx1.right <| Eq.symm hx2.right
        apply h2 x1 (Set.mem_toFinset.mpr hx1.left) x2 (Set.mem_toFinset.mpr hx2.left) at this
        contradiction
      have h4 (a :  Finset.range p) (ha : a ∈ finset_p_non_zero.toFinset) : (a.val * (σ a).val) % p = i a ha := by simp [i]
      exact Finset.prod_bij i h1 h2 h3 h4

    -- prove ∏ x ∈ [1, k] = k!
    have k_prod (k : ℕ) : ∏ x ∈ Finset.Icc 1 k, x = Nat.factorial k := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Finset.prod_Icc_succ_top, ih, Nat.factorial_succ]; ring; exact Nat.le_add_left 1 k

    -- prove ∏ x ∈ [1, p-1], x = (p - 1)!
    have prod_reorder : ∏ x ∈ finset_p_non_zero, x.val = ∏ x ∈ Finset.Icc 1 (p - 1), x := by
      let i (a : Finset.range p) (_ : a ∈ finset_p_non_zero.toFinset) : ℕ := a.val
      have h1 (a : Finset.range p) (ha : a ∈ finset_p_non_zero.toFinset) : i a ha ∈ Finset.Icc 1 (p - 1) := by
        simp [finset_p_non_zero] at ha
        obtain ⟨a, ha'⟩ := a
        simp [zero_fin] at ha' ha
        simp [i, ha', ha]
        constructor
        · exact Nat.one_le_iff_ne_zero.mpr ha
        · exact Nat.le_sub_one_of_lt ha'
      have h2 (a₁ : Finset.range p) (ha₁ : a₁ ∈ finset_p_non_zero.toFinset)
          (a₂ : Finset.range p) (ha₂ : a₂ ∈ finset_p_non_zero.toFinset) (h : i a₁ ha₁ = i a₂ ha₂) : a₁ = a₂ := by
        simp [i] at h
        exact Subtype.coe_inj.mp h
      have h3 (b : ℕ) (h : b ∈ Finset.Icc 1 (p - 1)) : ∃ a, ∃ (ha : a ∈ finset_p_non_zero.toFinset), i a ha = b := by
        simp at h
        obtain ⟨h1, h2⟩ := h
        have : b ∈ Finset.range p := by simp; refine (Nat.le_sub_one_iff_lt ?_).mp h2; exact Nat.Prime.pos hp
        use ⟨b, this⟩
        have hin : ⟨b, this⟩ ∈ finset_p_non_zero.toFinset := by
          simp [finset_p_non_zero, zero_fin]; by_contra heq; rw [heq] at h1; contradiction
        use hin
      have h4 (a : Finset.range p) (ha : a ∈ finset_p_non_zero.toFinset) : a = i a ha := by simp [i]
      exact Finset.prod_bij i h1 h2 h3 h4

    -- prove ∏ x ∈ [1, p-1] σ x = ∏ x ∈ [1, p-1] x
    have prod_congr : ∏ x ∈ finset_p_non_zero, (σ x).val = ∏ x ∈ finset_p_non_zero, x.val := by
      refine Equiv.Perm.prod_comp σ finset_p_non_zero.toFinset Subtype.val ?hs
      intro a ha
      by_contra hnin
      simp [finset_p_non_zero] at hnin ha
      rw [hnin] at ha
      contradiction

    have mod_to_mod (x : ℕ) : x % p = (x : ZMod p) := by simp

    -- obtain that ∏ x ∈ [1, p-1], σ x * x ≡ ∏ x ∈ [1, p-1], σ x * ∏ x ∈ [1, p-1], x = (p-1)! ^ 2 ≡ 1 (mod p) by wilson lemma
    have prod_res_mod1 : (∏ x ∈ finset_p_non_zero, (x.val * (σ x).val) % p : ZMod p) = 1 := by
      simp [mod_to_mod]
      norm_cast
      rw [Finset.prod_mul_distrib, prod_congr, prod_reorder, k_prod (p - 1)]
      simp

    -- obtaint that ∏ x ∈ [1, p-1] σ x * x ≡ (p - 1)! ≡  -1 (mod p) by wilson lemma
    have prod_res_mod2 : (∏ x ∈ finset_p_non_zero, (x.val * (σ x).val) % p : ZMod p) = -1 := by
      rw [<-ZMod.wilsons_lemma p, <-k_prod (p - 1), <-prod_reorder, <-prod_f]
      simp

    -- therfore, -1 ≡ 1 (mod p)
    have : -1 = (1 : ZMod p) := by
      nth_rw 2 [<-prod_res_mod1]
      rw [<-prod_res_mod2]

    have : 2 = (0 : ZMod p) := by
      calc
        (2 : ZMod p) = 1 + 1 := by exact Eq.symm one_add_one_eq_two
        _ = 1 + (-1) := by nth_rw 2 [<-this]
        _ = 0 := by simp

    -- 2 ∣ p
    have : p ∣ 2 := by exact (ZMod.natCast_zmod_eq_zero_iff_dvd 2 p).mp this

    -- since p is a prime, p = 2
    have : p = 2 := by exact Nat.prime_dvd_prime_iff_eq hp (show Nat.Prime 2 by decide) |>.mp this

    -- contradicts the fact that p is odd
    rw [this] at hodd
    contradiction

  -- proj any m into [0, p-1] by %p
  let proj (x : Finset.Icc 1 p) : Finset.range p := ⟨(m x) % p, in_finset (m x)⟩

  -- show that proj is a bijection
  have proj_bij : Function.Bijective proj := by
    obtain ⟨m₀, hm⟩ := hm
    have hp''' : p ≥ 1 := by exact NeZero.one_le
    have hp'' : p - 1 < p := by apply Nat.sub_one_lt_of_lt; exact Nat.pos_of_neZero p
    constructor
    · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp [proj, hm ⟨a, ha⟩, hm ⟨b, hb⟩] at hab ⊢
      simp at ha hb
      have : m₀ + a = m₀ + b := by
        apply eq_of_mod p (m₀ + a) (m₀ + b)
        · calc
            m₀ + a ≤ m₀ + (1 + (p - 1)) := by simp [Nat.add_sub_cancel' hp''']; rel [ha.right]
            _ ≤ m₀ + (b + (p - 1)) := by rel [hb.left]
            _ < m₀ + (b + p) := by rel [hp'']
            _ = m₀ + b + p := by linarith
        · calc
            m₀ + b ≤ m₀ + (1 + (p - 1)) := by simp [Nat.add_sub_cancel' hp''']; rel [hb.right]
            _ ≤ m₀ + (a + (p - 1)) := by rel [ha.left]
            _ < m₀ + (a + p) := by rel [hp'']
            _ = m₀ + a + p := by linarith
        · exact hab
      simp [add_left_inj] at this
      exact this
    · intro ⟨y, hy⟩
      simp at hy
      by_cases hm₀ : m₀ % p < y
      · let i := y - m₀ % p
        have : i ∈ Finset.Icc 1 p := by
          simp [i] at *
          constructor
          · exact Nat.le_sub_of_add_le' hm₀
          · refine Nat.le_add_right_of_le ?right.h; exact Nat.le_of_succ_le hy
        use ⟨i, this⟩
        simp [proj, i, hm, Nat.add_mod]
        rw [Nat.mod_mod, Nat.mod_mod]
        have : (y - m₀ % p) % p = (y - m₀ % p) := by apply Nat.mod_eq_of_lt; exact tsub_lt_of_lt hy
        rw [this, Nat.add_sub_cancel']
        · apply Nat.mod_eq_of_lt hy
        · exact Nat.le_of_succ_le hm₀
      · push_neg at hm₀
        let i := y + p - m₀ % p
        have : m₀ % p < p := by exact Nat.mod_lt m₀ hp'''
        have hi : i ∈ Finset.Icc 1 p := by
          simp [i] at *
          constructor
          · calc
              1 ≤ p - m₀ % p := by exact Nat.le_sub_of_add_le' this
              _ ≤ y + (p - m₀ % p) := by exact Nat.le_add_left (p - m₀ % p) y
              _ = y + p - m₀ % p := by rw [Nat.add_sub_assoc]; exact Nat.le_of_succ_le this
          · rw [add_comm]; exact Nat.add_le_add_left hm₀ p
        use ⟨i, hi⟩
        simp [proj, i, hm, Nat.add_mod]
        rw [Nat.mod_mod, Nat.mod_mod]
        rcases gt_or_eq_of_le hm₀ with hgt | heq
        · have heq : (y + p - m₀ % p) % p = (y + p - m₀ % p) := by
            apply Nat.mod_eq_of_lt
            calc
              y + p - m₀ % p = y + (p - m₀ % p) := by rw [Nat.add_sub_assoc]; exact Nat.le_of_succ_le this
              _ < m₀ % p + (p - m₀ % p) := by rel [hgt]
              _ = p := by rw [Nat.add_sub_cancel']; exact Nat.le_of_succ_le this
          rw [heq]
          rw [Nat.add_sub_cancel']
          · simp; exact Nat.mod_eq_of_lt hy
          · calc
              m₀ % p ≤ p := by exact Nat.le_of_succ_le this
              _ ≤ y + p := by exact Nat.le_add_left p y
        · simp [heq]
          exact Nat.mod_eq_of_lt hy

  -- therefore proj induces a equiv
  let ρ : Equiv (Finset.Icc 1 p) (Finset.range p) := Equiv.ofBijective proj proj_bij

  -- σ' = ρ⁻¹ σ ρ  is a permutation on [0, p-1]
  let σ' := Equiv.trans (Equiv.symm ρ) (Equiv.trans σ ρ)

  -- apply the lemma
  obtain ⟨k, ⟨l, ⟨hkl, hdvd⟩⟩⟩ := case_for_range_p σ'

  -- recover k' = ρ⁻¹ k, l' = ρ⁻¹ l
  let k' := (Equiv.symm ρ) k
  let l' := (Equiv.symm ρ) l

  -- show that if y = ρ x, then m x ≡ y (mod p)
  have ρ_congr (x : Finset.Icc 1 p) (y : Finset.range p) (hxy : y = ρ x) : m x = (y : ZMod p) := by
    obtain ⟨y, hy⟩ := y
    obtain ⟨x, hx⟩ := x
    simp [ρ, proj] at hxy
    simp [hxy]

  -- since p ∣ k * (σ' k) - l * (σ' l), replacing k l by k' l', we have p ∣ (m k') * (m (σ k')) - (m l') * (m (σ l'))
  have mod_eq_0 : (m k') * (m (σ k')) - (m l') * (m (σ l')) = (0 : ZMod p) := by
    have h1 : m k' = (k : ZMod p) := by apply ρ_congr k' k; simp [k']
    have h2 : m l' = (l : ZMod p) := by apply ρ_congr l' l; simp [l']
    have h3 : m (σ k') = (σ' k : ZMod p) := by apply ρ_congr (σ k') (σ' k); simp [k', σ']
    have h4 : m (σ l') = (σ' l : ZMod p) := by apply ρ_congr (σ l') (σ' l); simp [l', σ']
    calc
      (m k') * (m (σ k')) - (m l') * (m (σ l')) = (k : ZMod p) * (σ' k) - l * (σ' l) := by simp [h1, h2, h3, h4]
      _ = (0 : ZMod p) := by
        obtain h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((k : ℤ) * (σ' k) - l * (σ' l)) p).mpr hdvd
        simp at h
        exact h

  -- show that k' ≠ l'
  have hkl' : k' ≠ l' := by exact fun a ↦ hkl ((Equiv.injective (Equiv.symm ρ)) a)
  use k', l', hkl'
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp [mod_eq_0]
