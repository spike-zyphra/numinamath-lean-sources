import Mathlib

open Finset

/- Some basic facts : if n is even, then 1 ≤ Nat.factorization n 2 -/
lemma one_le_factorization_of_even {n : ℕ} (heven : Even n) (hn : n > 0) : 1 ≤ Nat.factorization n 2 := by
  have : 2 ^ 1 ∣ n := by
    simp
    exact even_iff_two_dvd.mp heven
  refine (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) ?_).mp this
  exact Nat.not_eq_zero_of_lt hn

/- (n / 2 ^ Nat.factorization n 2) is odd. -/
lemma odd_div_factorization {n : ℕ} (hn : n > 0) : Odd (n / 2 ^ Nat.factorization n 2) := by
  by_contra h
  simp at h
  have : 2 ^ (Nat.factorization n 2 + 1) ∣ n := by
    rw [Nat.pow_add_one]
    apply Nat.mul_dvd_of_dvd_div
    · exact Nat.ordProj_dvd n 2
    · exact even_iff_two_dvd.mp h
  have : ¬ 2 ^ (Nat.factorization n 2 + 1) ∣ n := by
    refine pow_succ_padicValNat_not_dvd ?_
    exact Nat.not_eq_zero_of_lt hn
  contradiction

/- If m and n are coprime and n is even, then m must be odd -/
lemma odd_of_coprime_even {m n : ℕ} (hn : Even n) (hco : m.Coprime n) : Odd m := by
  have : 2 ∣ n := by exact even_iff_two_dvd.mp hn
  have : ¬ 2 ∣ m := by
    by_contra h
    have : ¬ m.Coprime n := by
      refine Nat.Prime.not_coprime_iff_dvd.mpr ?_
      use 2, (by norm_num)
    contradiction
  refine Nat.odd_iff.mpr ?_
  exact Nat.two_dvd_ne_zero.mp this

/- Prove that f maps from SN to SN, where SN = {s ∈ S | s.1 + s.2 =N } -/
lemma mapsTo_f_SN_SN {f : ℕ × ℕ → ℕ × ℕ} {SN : Set (ℕ × ℕ)} (hS : SN = {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n ∧ m + n = N})
    (hf : ∀ m n, f (m, n) = (n / 2 ^ (Nat.factorization n 2), m + n - n / 2 ^ (Nat.factorization n 2))) :
    Set.MapsTo f SN SN := by
  intro ⟨m, n⟩ hs
  rw [hS] at hs ⊢
  obtain ⟨hm, hlt, hn, hco, hN⟩ := hs
  rw [hf]
  split_ands
  · -- n / 2 ^ n.factorization 2 > 0
    apply Nat.div_pos
    · apply Nat.le_of_dvd
      · exact Nat.zero_lt_of_lt hlt
      · exact Nat.ordProj_dvd n 2
    · positivity
  · --  n / 2 ^ n.factorization 2 * 2  ≤ n < m + n 
    apply Nat.lt_sub_of_add_lt
    apply lt_of_le_of_lt (b := n / 2 + n / 2)
    · gcongr
      all_goals
        apply le_of_eq_of_le (b := 2 ^ 1) (by simp)
        gcongr
        · simp
        · apply one_le_factorization_of_even hn
          exact Nat.zero_lt_of_lt hlt
    · ring_nf
      rw [Nat.div_mul_cancel (by exact even_iff_two_dvd.mp hn)]
      simp [hm]
  · -- m + n - n / 2 ^ n.factorization 2 is even
    apply Nat.Odd.sub_odd
    · apply Odd.add_even ?_ hn
      exact odd_of_coprime_even hn hco
    · refine odd_div_factorization ?_
      exact Nat.zero_lt_of_lt hlt
  · -- (n / 2 ^ n.factorization 2).Coprime (m + n - n / 2 ^ n.factorization 2)
    apply Nat.coprime_sub_self_right ?_ |>.mpr
    · apply Nat.Coprime.coprime_div_left
      · apply Nat.coprime_add_self_right.mpr
        exact Nat.coprime_comm.mp hco
      · exact Nat.ordProj_dvd n 2
    · apply le_add_of_le_right
      exact Nat.ordCompl_le n 2
  · -- n / 2 ^ n.factorization 2 + (m + n - n / 2 ^ n.factorization 2) = N
    rw [Nat.add_sub_cancel', hN]
    apply le_add_of_le_right
    exact Nat.ordCompl_le n 2

/- Also $f$ is bijective -/
lemma bijOn_f_SN {f : ℕ × ℕ → ℕ × ℕ} {SN : Set (ℕ × ℕ)} (hS : SN = {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n ∧ m + n = N})
    (hf : ∀ m n, f (m, n) = (n / 2 ^ (Nat.factorization n 2), m + n - n / 2 ^ (Nat.factorization n 2))) :
    Set.BijOn f SN SN := by
  refine (Set.Finite.surjOn_iff_bijOn_of_mapsTo ?_ ?_).mp ?_
  · -- Prove that SN is finite
    refine Set.finite_image_fst_and_snd_iff.mp ?_
    constructor
    all_goals
      refine Set.finite_iff_bddAbove.mpr ?_
      use N
      intro r hr
      simp [hS] at hr
      obtain ⟨_, _, hr⟩ := hr
      rw [←hr.2.2.2]
      simp
  · -- Since f maps from SN to SN, we only need to prove that f is surjective
    exact mapsTo_f_SN_SN hS hf
  · intro ⟨m, n⟩ h
    simp [hS] at h
    obtain ⟨hm, hn, he, hco, hN⟩ := h
    have hodd_N : Odd N := by
      rw [←hN]
      apply Odd.add_even ?_ he
      exact odd_of_coprime_even he hco
    -- There must exists some n' and k such that n' = 2 ^ k * m and n' > N / 2 and n' < N.
    obtain ⟨n', k, hk, hn', hn'_gt, hn'_lt⟩ : ∃ n k, k ≥ 1 ∧ n = 2 ^ k * m ∧ n > N / 2 ∧ n < N := by
      let p (k : ℕ) := 2 ^ k * m > N / 2
      have hp : ∃ k, p (k + 1) := by
        use N
        apply lt_of_lt_of_le (b := 2 ^ (N + 1))
        · apply lt_of_lt_of_le (b := N + 1)
          · apply Nat.lt_succ_of_le
            exact Nat.div_le_self N 2
          · clear * -
            induction N with
            | zero => simp
            | succ N ih =>
              trans 2 ^ (N + 1) + 2 ^ (N + 1)
              · gcongr
                exact Nat.one_le_two_pow
              · apply le_of_eq; ring
        · simp
          exact hm
      let k := Nat.find hp
      have hk : 2 ^ (k + 1) * m > N / 2 := by apply Nat.find_spec hp
      use 2 ^ (k + 1) * m, k + 1
      simp [hk]
      by_contra h
      simp at h
      have hk' : k ≥ 1 := by
        by_contra h'
        simp at h'
        simp [h', ←hN] at h
        have : ¬ m + n ≤ m + m := by simp [hn]
        ring_nf at this h
        contradiction
      have : N + 1 ≤ 2 ^ (k + 1) * m := by
        by_contra h'
        simp at h'
        have : N = 2 ^ (k + 1) * m := by
          apply le_antisymm h
          exact Nat.le_of_lt_succ h'
        have : 2 ∣ N := by
          rw [this]
          simp [Nat.pow_add_one', mul_assoc]
        have : ¬ Odd N := by simp; apply even_iff_two_dvd.mpr this
        contradiction
      have : (N + 1) / 2 ≤ 2 ^ k * m := by
        apply Nat.div_le_of_le_mul
        apply le_of_le_of_eq this
        ring
      have : p (k - 1 + 1) := by
        rw [Nat.sub_add_cancel hk']
        apply lt_of_lt_of_le ?_ this
        suffices : N / 2 * 2 < (N + 1) / 2 * 2
        · simp at this
          exact this
        · apply lt_of_le_of_lt (b := N)
          · exact Nat.div_mul_le_self N 2
          · apply Nat.lt_of_succ_le
            apply Nat.le_of_eq
            rw [Nat.div_mul_cancel]
            suffices : Even (N + 1)
            · exact even_iff_two_dvd.mp this
            · apply Odd.add_odd ?_ (by exact Nat.odd_iff.mpr rfl)
              rw [←hN]
              apply Odd.add_even ?_ he
              exact odd_of_coprime_even he hco
      have : k - 1 ≥ k := by apply Nat.find_le; exact this
      have : ¬ k - 1 ≥ k := by simp; exact hk'
      contradiction
    -- Then we can prove that f (N - n', n') = (m, n)
    use ⟨N - n', n'⟩
    constructor
    · simp [hS]
      split_ands
      · exact hn'_lt
      · apply Nat.sub_lt_left_of_lt_add (le_of_lt hn'_lt)
        apply lt_of_lt_of_le (b := N / 2 + 1 + (N / 2 + 1))
        · ring_nf
          apply lt_of_eq_of_lt (b := N / 2 * 2 + N % 2)
          · exact Eq.symm (Nat.div_add_mod' N 2)
          · simp [Nat.add_comm]
            apply Nat.mod_lt
            simp
        · gcongr
          all_goals exact hn'_gt
      · rw [hn']
        refine Nat.even_mul.mpr ?_; left
        refine (Nat.even_pow' (by exact Nat.not_eq_zero_of_lt hk)).mpr (by exact Nat.even_iff.mpr rfl)
      · apply Nat.coprime_sub_self_left ?_ |>.mpr
        · rw [hn']
          refine Nat.Coprime.mul_right ?_ ?_
          · refine Nat.Prime.coprime_pow_of_not_dvd (by norm_num) ?_
            exact Odd.not_two_dvd_nat hodd_N
          · rw [←hN, add_comm]
            apply Nat.coprime_add_self_left.mpr
            exact Nat.coprime_comm.mp hco
        · exact Nat.le_of_succ_le hn'_lt
      · rw [Nat.sub_add_cancel (le_of_lt hn'_lt)]
    · have : Nat.factorization n' 2 = k := by
        rw [hn', Nat.factorization_mul, Nat.Prime.factorization_pow]
        simp
        apply Nat.factorization_eq_zero_of_not_dvd
        · refine Odd.not_two_dvd_nat ?_
          exact odd_of_coprime_even he hco
        · norm_num
        · positivity
        · exact Nat.not_eq_zero_of_lt hm
      rw [hf, this, hn', ←hN]
      simp
      rw [Nat.sub_add_cancel, Nat.add_sub_cancel_left]
      rw [hN, ←hn']
      exact Nat.le_of_succ_le hn'_lt

/- If f^[a] s = f^[b] s, then f^[b-a] s = s. -/
lemma f_cancel {f : ℕ × ℕ → ℕ × ℕ} {SN : Set (ℕ × ℕ)} (hS : SN = {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n ∧ m + n = N})
    (hf : ∀ m n, f (m, n) = (n / 2 ^ (Nat.factorization n 2), m + n - n / 2 ^ (Nat.factorization n 2))) (hs : s ∈ SN) (heq : f^[a] s = f^[b] s) :
    f^[b - a] s = s := by
  let F (x : SN) : SN := ⟨f x.1, mapsTo_f_SN_SN hS hf x.2⟩
  have hF {k : ℕ} : f^[k] s = F^[k] ⟨s, hs⟩ := by
    induction k with
    | zero => simp
    | succ k ih => simp only [Function.iterate_succ', Function.comp_apply, ih]
  have heq : F^[a] ⟨s, hs⟩ = F^[b] ⟨s, hs⟩ := by
    rw [hF, hF] at heq
    exact SetCoe.ext heq
  have : ⟨s, hs⟩ = F^[b - a] ⟨s, hs⟩ := by
    refine Eq.symm (Function.iterate_cancel ?_ (id (Eq.symm heq)))
    intro ⟨x, hx⟩ ⟨y, hy⟩ h
    simp [F] at h
    simp
    apply Set.BijOn.injOn (bijOn_f_SN hS hf) hx hy h
  simp [hF, ←this]

/- The cardinity of odd numbers in [0, n] are (n + 1) /2 -/
lemma card_odd {n : ℕ} : ((Icc 0 n).filter Odd).card = (n + 1) / 2 := by
  induction n with
  | zero =>
    simp
    ext x; simp
    intro hx
    simp [hx]
  | succ n ih =>
    have : filter Odd (Icc 0 (n + 1)) = ((Icc 0 n).filter Odd) ∪ (if Odd (n + 1) then {n + 1} else ∅) := by
      ext x
      simp [←Nat.Icc_insert_succ_right]
      constructor <;> intro hx
      · simp [hx.2]
        rcases hx.1 with h | h
        · right
          simp [h] at hx ⊢
          simp [hx]
        · simp [h]
      · rcases hx with h | h
        · simp [h]
        · by_cases h' : Odd (n + 1)
          · simp [h'] at h
            simp [h, h']
          · simp [h'] at h
    simp [this]
    rw [card_union_of_disjoint, ih]
    · by_cases h : Odd (n + 1)
      · simp [h]
        nth_rw 2 [←Nat.div_add_mod (n + 1) 2]
        simp [show (n + 1) % 2 = 1 by exact Nat.odd_iff.mp h, add_assoc]
      · simp [h]
        simp at h
        nth_rw 2 [←Nat.div_add_mod (n + 1) 2]
        simp [show (n + 1) % 2 = 0 by exact Nat.even_iff.mp h]
        rw [add_comm (2 * ((n + 1) / 2)), Nat.add_mul_div_left]
        · simp
        · simp
    · apply disjoint_left.mpr
      intro x hx
      simp at hx
      split_ifs
      · by_contra h
        simp at h
        simp [h] at hx
      · simp

/- The cardinity of even numbers in [0, n] are n + 1 - (n + 1) /2 -/
lemma card_even_eq {n : ℕ} : ((Icc 0 n).filter Even).card = (n + 1) - (n + 1) / 2 := by
  have : ((Icc 0 n).filter Even) ∪ (Icc 0 n).filter Odd = Icc 0 n := by
    ext x
    simp
    constructor <;> intro hx
    · rcases hx with hx | hx <;> simp [hx.1]
    · simp [hx]
      exact Nat.even_or_odd x
  apply congrArg card at this
  rw [card_union_of_disjoint, card_odd] at this
  · simp at this
    exact Nat.eq_sub_of_add_eq this
  · apply disjoint_filter.mpr
    simp

/- The cardinity of even numbers in (n / 2, n] are (n + 1) / 4 if n is odd. -/
lemma card_even (hodd : Odd N) : #(filter Even (Ioc (N / 2) N)) = (N + 1) / 4 := by
  have : (Ioc (N / 2) N).filter Even = ((Icc 0 N).filter Even) \ (Icc 0 (N / 2)).filter Even := by
    ext x
    simp
    constructor <;> intro hx
    · simp [hx]
    · simp [hx]
      by_contra h
      simp at h
      simp [h] at hx
      have : ¬ Odd x := by simp [hx.1.2]
      exact this.elim hx.2
  rw [this, card_sdiff, card_even_eq, card_even_eq]
  · set k := N / 2
    have hN : N = k * 2 + 1 := by
      rw [←Nat.div_add_mod' N 2]
      congr
      exact Nat.odd_iff.mp hodd
    have hN' : (N + 1) / 2 = k + 1 := by
      rw [hN, add_assoc]
      trans (k + 1) * 2 / 2
      · ring_nf
      · simp
    have hN'' : (N + 1) / 4 = (k + 1) / 2 := by
      trans (N + 1) / 2 / 2
      · rw [Nat.div_div_eq_div_mul]
      · rw [hN']
    have : (k + 1) / 2 ≤ k + 1 := by
      trans (k + 1) / 2 + (k + 1) / 2
      · simp
      · ring_nf
        exact Nat.div_mul_le_self (1 + k) 2
    rw [hN', hN'', hN]
    rw [Nat.sub_sub, ←Nat.add_sub_assoc this]
    ring_nf at this ⊢
    rw [Nat.sub_sub_self]
    apply le_trans this
    trans 2 * (1 + k)
    · simp
    · ring_nf
      simp
  · intro x hx
    simp at hx ⊢
    simp [hx.2]
    apply le_trans hx.1
    trans N / 2 + N / 2
    · simp
    · ring_nf
      exact Nat.div_mul_le_self N 2

/- We prove that ∀ s ∈ SN, ∃ t, t > 0 ∧ t ≤ (s.1 + s.2 + 1) / 4 ∧ f^[t] s = s. -/
lemma exists_nth_apply_eq {f : ℕ × ℕ → ℕ × ℕ} {SN : Set (ℕ × ℕ)} (hS : SN = {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n ∧ m + n = N})
    (hf : ∀ m n, f (m, n) = (n / 2 ^ (Nat.factorization n 2), m + n - n / 2 ^ (Nat.factorization n 2))) :
    ∀ s ∈ SN, ∃ t, t > 0 ∧ t ≤ (s.1 + s.2 + 1) / 4 ∧ f^[t] s = s := by
  intro x hx
  -- SN is finite and its cardinality is at most (N + 1) / 4.
  have hfin : SN.Finite := by
    refine Set.finite_image_fst_and_snd_iff.mp ?_
    constructor
    all_goals
      refine Set.finite_iff_bddAbove.mpr ?_
      use N
      intro r hr
      simp [hS] at hr
      obtain ⟨_, _, hr⟩ := hr
      rw [←hr.2.2.2]
      simp
  have ⟨s, hs⟩ : ∃ s : Finset (ℕ × ℕ), s = SN := by exact Set.Finite.exists_finset_coe hfin
  have hmem_s {x : ℕ × ℕ} : x ∈ s ↔ x ∈ SN := by simp [←hs]
  have hcard_s : s.card ≤ (N + 1) / 4 := by
    have h : s.card = (s.image Prod.fst).card := by
      refine Eq.symm (Finset.card_image_of_injOn ?_)
      intro a ha b hb h
      simp [hmem_s, hS] at ha hb
      have : a.1 + a.2 = b.1 + b.2 := by rw [ha.2.2.2.2, hb.2.2.2.2]
      simp [h] at this
      exact Prod.ext h this
    rw [h]
    have : s.image Prod.fst ⊆ (Icc 0 (N / 2)).filter Odd := by
      intro m hm
      simp at hm
      obtain ⟨x, hx⟩ := hm
      simp [hmem_s, hS] at hx
      obtain ⟨_, hlt, he, hco, hN⟩ := hx
      simp
      constructor
      · by_contra h
        simp at h
        have : m + x > N := by
          apply lt_of_le_of_lt (b := m + m)
          · ring_nf
            rw [←Nat.div_add_mod' N 2]
            trans (N / 2 + 1) * 2
            · simp [add_mul]
              apply le_of_lt
              apply Nat.mod_lt
              simp
            · simp
              exact h
          · simp [hlt]
        simp [hN] at this
      · exact odd_of_coprime_even he hco
    apply card_le_card at this
    simp [card_odd] at this
    apply le_trans this
    have : Odd N := by
      simp [hS] at hx
      rw [←hx.2.2.2.2]
      apply Odd.add_even ?_ hx.2.2.1
      exact odd_of_coprime_even hx.2.2.1 hx.2.2.2.1
    have : N = N / 2 * 2 + 1 := by
      nth_rw 1 [← Nat.div_add_mod' N 2]
      simp
      exact Nat.odd_iff.mp this
    nth_rw 2 [this]
    simp [add_assoc]
    apply le_of_eq
    trans ((N / 2 + 1) * 2) / (2 * 2)
    · rw [Nat.mul_div_mul_right]; simp
    · simp [add_mul]
  -- Consider t = [1, (N + 1) / 4 + 1], and g(k) = f^[k] x, which maps from t to SN
  let t := Icc 1 ((N + 1) / 4 + 1)
  have hcard_t : t.card = (N + 1) / 4 + 1 := by simp [t]
  let g (k : ℕ) := f^[k] x
  have hg : ∀ k ∈ t, g k ∈ s := by
    intro k _
    simp [g]
    clear * - hx hf hS hmem_s
    induction k with
    | zero => simp [hmem_s, hx]
    | succ k ih =>
      simp only [Function.iterate_succ', Function.comp_apply, hmem_s]
      apply mapsTo_f_SN_SN hS hf
      simp [←hmem_s, ih]
  -- SInce #t > #s, we can find some a b ∈ t such that g a = g b
  have hcard_lt : t.card > s.card * 1:= by simp [hcard_t]; exact Order.lt_add_one_iff.mpr hcard_s
  obtain ⟨_, _, h⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hg hcard_lt
  obtain ⟨a, ha, b, hb, hne⟩ := one_lt_card.mp h
  -- wlog assume a < b
  wlog hsr : a < b generalizing a b with H
  · simp at hsr
    have : b < a := by exact Nat.lt_of_le_of_ne hsr (id (Ne.symm hne))
    exact H b hb a ha (by exact id (Ne.symm hne)) this
  · -- Then we have f^[a] x = f^[b] x.
    -- Therefore, f^[b - a] x = x.
    simp at ha hb
    have heq : g a = g b := by simp [ha, hb]
    unfold g at heq
    have : f^[b - a] x = x := by exact f_cancel hS hf hx heq
    -- Note that b - a > 0 and b - a ≤ (N + 1) / 4 + 1.
    use b - a
    split_ands
    · exact Nat.zero_lt_sub_of_lt hsr
    · simp [t] at ha hb
      trans (N + 1) / 4 + 1 - 1
      · gcongr
        · exact hb.1.2
        · exact ha.1.1
      · simp [hS] at hx ⊢
        rw [hx.2.2.2.2]
    · exact this

/- If n ∣ N and N ≠ 0, then padicValNat p n ≤ padicValNat p N -/
lemma padic_le_of_dvd {n : ℕ} {p : ℕ} [hp : Fact (Nat.Prime p)] (hdvd : n ∣ N) (hN : N ≠ 0) :
    padicValNat p n ≤ padicValNat p N := by
  have : p ^ (padicValNat p n) ∣ n := by exact pow_padicValNat_dvd
  apply dvd_trans this at hdvd
  exact padicValNat_dvd_iff_le hN |>.mp hdvd

/- (2 * m)!! is the production of all even numbers in (0, 2 * m]. -/
lemma doubleFactorial_eq_prod_even : (2 * m).doubleFactorial = ((Ioc 0 (2 * m)).filter Even).prod id := by
  rw [Nat.doubleFactorial_eq_prod_even]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ, ih]
    have : filter Even (Ioc 0 (2 * (m + 1))) = filter Even (Ioc 0 (2 * m)) ∪ {2 * (m + 1)} := by
      ext x
      simp
      constructor <;> intro hx
      · simp [hx]
        rcases lt_or_eq_of_le hx.1.2 with h | h
        · left; by_contra h'
          simp at h'
          have : x = 2 * m + 1 := by exact Nat.eq_of_le_of_lt_succ h' h
          rw [this] at hx
          have : ¬ Even (2 * m + 1) := by simp
          exact this.elim hx.2
        · simp [h]
      · rcases hx with h | h
        · simp [h]
          apply le_trans h.1.2
          simp
        · simp [h]
    rw [this, prod_union]
    · simp
    · simp

/- We prove that padicValNat 2 (((Ioc (N / 2) N).filter Even).prod id) = (N - 1) / 2 when N is odd. -/
lemma padic_prod {N : ℕ} (hodd : Odd N) : padicValNat 2 (((Ioc (N / 2) N).filter Even).prod id) = (N - 1) / 2  := by
  -- First, show that padicValNat 2 (2 * n).doubleFactorial = padicValNat 2 (2 * n).factorial
  have padic_fact {n : ℕ} : padicValNat 2 (2 * n).doubleFactorial = padicValNat 2 (2 * n).factorial := by
    by_cases hn : n = 0
    · simp [hn]
    · have : 2 * n = 2 * (n - 1) + 2 := by
        rw [Nat.mul_sub, Nat.sub_add_cancel]
        simp
        exact Nat.one_le_iff_ne_zero.mpr hn
      rw [this, Nat.factorial_eq_mul_doubleFactorial]
      rw [padicValNat.mul]
      · simp; right
        suffices : ¬ 2 ∣ (2 * (n - 1) + 1).doubleFactorial
        · exact Nat.two_dvd_ne_zero.mp this
        · rw [Nat.doubleFactorial_eq_prod_odd]
          apply Prime.not_dvd_finset_prod
          · refine Nat.prime_iff.mp ?_; norm_num
          · simp
      · positivity
      · positivity
  -- Then, padicValNat 2 ((2 * n).doubleFactorial / (2 * m).doubleFactorial) = padicValNat 2 (2 * n).factorial - padicValNat 2 (2 * m).factorial
  -- = (2 * n) / 2 + (2 * n) / 4 + ... - (2 * m / 2 + (2 * m) / 4 + ...)
  -- = n
  have padic_fact_div {m n : ℕ} (hm : m = n / 2) : padicValNat 2 ((2 * n).doubleFactorial / (2 * m).doubleFactorial) = n := by
    let b := Nat.log 2 (2 * n) + 1
    have hb₁ : Nat.log 2 (2 * n) < b := by simp [b]
    have hb₂ : Nat.log 2 (2 * m) < b := by
      apply lt_of_le_of_lt ?_ hb₁
      apply Nat.log_monotone
      rw [hm]
      trans n
      · exact Nat.mul_div_le n 2
      trans n + n
      · simp
      · ring_nf; simp
    have hb₁ : Nat.log 2 (2 * n) < b + 1 := by exact Nat.lt_add_right 1 hb₁
    rw [padicValNat.div_of_dvd, padic_fact, padic_fact, padicValNat_factorial hb₁, padicValNat_factorial hb₂]
    · have : Ico 1 (b + 1) = {1} ∪ Ico (1 + 1) (b + 1) := by
        ext x; simp
        constructor <;> intro hx
        · simp [hx.2]
          rcases eq_or_lt_of_le hx.1 with h | h
          · simp [h]
          · have : 2 ≤ x := by exact h
            simp [this]
        · rcases hx with h | h
          · simp [h]
          · constructor
            · apply le_trans (by simp) h.1
            · exact h.2
      rw [this, sum_union]
      · simp
        have : (Ico 1 b).image (fun x => x + 1) = Ico 2 (b + 1) := by
          ext x
          simp
        rw [←this, sum_image]
        · apply Nat.sub_eq_of_eq_add
          simp
          apply sum_congr rfl
          intro x hx
          simp [pow_add]
          rw [mul_comm, Nat.mul_div_mul_right]
          · simp at hx
            have : x = x - 1 + 1 := by rw [Nat.sub_add_cancel hx.1]
            rw [this, pow_add]
            simp
            rw [mul_comm, ←Nat.div_div_eq_div_mul, mul_comm, ←Nat.div_div_eq_div_mul]
            simp [hm]
          · simp
        · simp
      · simp
    · simp [Nat.doubleFactorial_eq_prod_even]
      apply prod_dvd_prod_of_subset
      simp [hm]
      exact Nat.div_le_self n 2
  -- Now, let n = N / 2 and m = n / 2, we can prove that (filter Even (Ioc n (n * 2 + 1))).prod id = (2 * n).doubleFactorial / (2 * m).doubleFactorial
  set n := N / 2
  have hN : N = n * 2 + 1 := by
    rw [←Nat.div_add_mod' N 2]
    congr
    exact Nat.odd_iff.mp hodd
  have hN' : (N - 1) / 2 = n := by
    rw [hN]
    simp
  let m := n / 2
  rw [hN', hN]
  have : (filter Even (Ioc n (n * 2 + 1))).prod id = (2 * n).doubleFactorial / (2 * m).doubleFactorial := by
    apply Nat.eq_div_of_mul_eq_left
    · positivity
    · rw [doubleFactorial_eq_prod_even, doubleFactorial_eq_prod_even]
      simp
      have : filter Even (Ioc n (n * 2 + 1)) = (filter Even (Ioc 0 (2 * n))) \ (filter Even (Ioc 0 (2 * m))) := by
        ext x
        simp
        constructor <;> intro hx
        · obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hx
          simp [h₃]
          split_ands
          · exact Nat.zero_lt_of_lt h₁
          · by_contra h
            simp at h
            have : x = n * 2 + 1 := by
              apply le_antisymm h₂
              rw [mul_comm]
              exact h
            simp [this] at h₃
            have : ¬ Even (n * 2 + 1) := by simp
            contradiction
          · intro _ hx
            have : ¬ n < x := by
              simp
              apply le_trans hx
              exact Nat.mul_div_le n 2
            contradiction
        · obtain ⟨⟨h₀, h₁⟩, h₂⟩ := hx
          simp [h₁]
          constructor
          · by_contra h
            simp at h
            have hm : x ≤ 2 * m := by
              by_contra h'
              simp at h'
              have : x ≥ 2 * m + 2 := by
                by_contra h''
                simp at h''
                have : x = 2 * m + 1 := by exact Nat.eq_of_le_of_lt_succ h' h''
                simp [this] at h₁
              apply le_trans this at h
              simp [m] at h
              nth_rw 2 [←Nat.div_add_mod' n 2] at h
              ring_nf at h
              simp [add_comm] at h
              have : ¬ 2 ≤ n % 2 := by
                simp
                apply Nat.mod_lt
                simp
              contradiction
            obtain h := h₂ h₀.1 hm
            have : ¬ Odd x := by simp [h₁]
            contradiction
          · apply le_trans h₀.2
            ring_nf
            simp
      rw [this, prod_sdiff]
      intro x hx
      simp at hx ⊢
      simp [hx]
      apply le_trans hx.1.2
      simp [m]
      exact Nat.div_le_self n 2
  rw [this]
  -- Therefore, padicValNat 2 ((2 * n).doubleFactorial / (2 * m).doubleFactorial) = n
  exact padic_fact_div rfl

/- If N is odd and n₀ ∈ ((Ioc (N / 2) N).filter Even), then padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) < (N - 1) / 2. -/
lemma padic_prod_erase (hn₀ : n₀ ∈ ((Ioc (N / 2) N).filter Even)) (hodd : Odd N) : padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) < (N - 1) / 2 := by
  --  (((Ioc (N / 2) N).filter Even).erase n₀).prod id * n₀ = ((Ioc (N / 2) N).filter Even).prod id since n₀ ∈ ((Ioc (N / 2) N).filter Even).
  have : (((Ioc (N / 2) N).filter Even).erase n₀).prod id * n₀ = ((Ioc (N / 2) N).filter Even).prod id := by
    have : (Ioc (N / 2) N).filter Even = (((Ioc (N / 2) N).filter Even).erase n₀) ∪ {n₀} := by
      ext x
      simp
      constructor <;> intro hx
      · simp [hx]
        exact ne_or_eq x n₀
      · rcases hx with h | h
        · simp [h]
        · simp [h]
          simp at hn₀
          exact hn₀
    nth_rw 2 [this]
    rw [prod_union]
    · simp
    · simp
  -- Then, padicValNat 2 (((Ioc (N / 2) N).filter Even).erase n₀).prod id = padicValNat 2 (((Ioc (N / 2) N).filter Even).prod id) - padicValNat 2 n₀
  -- Since n₀ ∈ ((Ioc (N / 2) N).filter Even), we have padicValNat 2 n₀ > 0.
  -- Therefore, padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) < padicValNat 2 (((Ioc (N / 2) N).filter Even).prod id) = (N - 1) / 2.
  apply congrArg (fun x => padicValNat 2 x) at this
  rw [padicValNat.mul, padic_prod] at this
  · rw [←this]
    simp
    apply Nat.lt_of_succ_le
    simp at hn₀
    rcases hn₀ with ⟨⟨h₁, _⟩, h₂⟩
    apply one_le_padicValNat_of_dvd
    · exact Nat.zero_lt_of_lt h₁
    · exact even_iff_two_dvd.mp h₂
  · exact hodd
  · simp
    by_contra h
    apply prod_eq_zero_iff.mp at h
    obtain ⟨a, ha, heq⟩ := h
    simp [heq] at ha
  · intro h
    simp [h] at hn₀

/- If N is a prime dividing N, and ∀ k ∈ Icc 1 (N - 2), ¬ N ∣ 2 ^ k - 1, then ∀ s ∈ SN, ∀ t, t > 0 ∧ f^[t] s = s → t ≥ (N + 1) / 4 -/
lemma le_of_nth_apply_eq {f : ℕ × ℕ → ℕ × ℕ} {SN : Set (ℕ × ℕ)} (hS : SN = {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n ∧ m + n = N})
    (hf : ∀ m n, f (m, n) = (n / 2 ^ (Nat.factorization n 2), m + n - n / 2 ^ (Nat.factorization n 2)))
    (hN : Nat.Prime N)
    (hndvd : ∀ k ∈ Icc 1 (N - 2), ¬ N ∣ 2 ^ k - 1) :
    ∀ s ∈ SN, ∀ t, t > 0 ∧ f^[t] s = s → t ≥ (N + 1) / 4 := by
  -- Assume that f^[t] s = s, then there exists t such that f^[t] s = s and t > 0.
  -- We can find the smallest t such that f^[t] s = s, and
  -- we prove that t ≥ (N + 1) / 4.
  intro s hs t ⟨ht, heq⟩
  let P (k : ℕ) := k > 0 ∧ f^[k] s = s
  have hP : ∃ t, P t := by use t
  let t := Nat.find hP
  have ht : t > 0 := (Nat.find_spec hP).1
  have heq' : f^[t] s = s := (Nat.find_spec hP).2
  have hle : ∀ k, P k → t ≤ k := by intro k hk; apply Nat.find_le hk
  suffices : t ≥ (N + 1) / 4
  · apply le_trans this
    apply hle
    constructor
    all_goals assumption
  · -- Otherwise, assume that t < (N + 1) / 4.
    by_contra hlt
    simp at hlt
    have hfk_mem : ∀ {k}, f^[k] s ∈ SN := by
      intro k
      induction k with
      | zero => simp [hs]
      | succ k ih =>
        simp only [Function.iterate_succ', Function.comp_apply]
        apply mapsTo_f_SN_SN hS hf ih
    simp [hS, forall_and] at hfk_mem
    obtain ⟨hm_pos, hn_gt_m, heven_n, hco_mn, hmn⟩ := hfk_mem
    have hodd_N : Odd N := by
      rw [←hmn 0]
      apply Odd.add_even ?_ (heven_n 0)
      apply odd_of_coprime_even (heven_n 0) (hco_mn 0)
    -- Define m k and n k as the first and second components of f^[k] s.
    -- Define a k as the factorization of 2 in n k
    let m (k : ℕ) := (f^[k] s).1
    let n (k : ℕ) := (f^[k] s).2
    let a (k : ℕ) := Nat.factorization (n k) 2
    -- Observe that n k = 2 ^ a k * m (k + 1) for all k.
    have hn_succ : ∀ k, n k = 2 ^ a k * m (k + 1) := by
      intro k
      simp only [n, m, Function.iterate_succ', Function.comp_apply, hf]
      rw [Nat.mul_div_cancel_left']
      exact Nat.ordProj_dvd (f^[k] s).2 2
    -- Also define ν = ∏ i ∈ range t, n i, μ = ∏ i ∈ range t, m i, and α = ∑ i ∈ range t, a i.
    let ν := ∏ i ∈ range t, n i
    let μ := ∏ i ∈ range t, m i
    let α := ∑ i ∈ range t, a i
    -- We have that ν = 2 ^ α * μ, and μ > 0.
    have hμ_pos : μ > 0 := by
      apply prod_pos
      intro i _
      apply hm_pos
    have hμ : ν = 2 ^ α * μ := by
      trans 2 ^ (∑ i ∈ range t, a i) * (∏ i ∈ range t, m (i + 1))
      · simp [ν, hn_succ, prod_mul_distrib]
        left
        rw [prod_pow_eq_pow_sum]
      · simp [μ]
        have ht : t = t - 1 + 1 := by rw [Nat.sub_add_cancel]; exact ht
        rw [ht]
        rw [prod_range_succ, prod_range_succ']
        simp; left
        rw [←ht]
        simp [m]
        congr
    -- Note that ν = ∏ (N - m i) ≡ (-1) ^ t * μ [ZMOD N].
    have hν : ν ≡ (-1) ^ t * μ [ZMOD N] := by
      simp [ν]
      trans ∏ i ∈ range t, (N - m i)
      · congr
        ext k
        apply eq_sub_of_add_eq
        norm_cast
        rw [add_comm]
        apply hmn
      trans ∏ i ∈ range t, (0 - m i)
      · apply ZMod.intCast_eq_intCast_iff _ _ _ |>.mp
        simp
      trans ∏ i ∈ range t, (-1) * m i
      · simp
      · rw [prod_mul_distrib]
        congr
        · simp
        · simp [μ]
    rw [hμ] at hν
    -- Therefore, we have 2 ^ (2 * α) * μ ^ 2 ≡ μ ^ 2 [ZMOD N].
    have hν : 2 ^ (2 * α) * μ ^ 2 ≡ μ ^ 2 [ZMOD N] := by
      trans ↑(2 ^ α * μ) ^ 2
      · congr
        simp; ring
      trans ((-1) ^ t * ↑μ) ^ 2
      · apply Int.ModEq.pow 2 hν
      · congr 1
        ring_nf
        rw [mul_comm _ 2, pow_mul]
        simp
    -- i.e., N ∣ 2 ^ (2 * α) - 1 since μ ^ 2 is coprime to N, where N is a prime.
    have hν : ↑N ∣ (2 ^ (2 * α) - 1 : ℤ) * μ ^ 2 := by
      simp [sub_mul]
      apply Int.ModEq.dvd
      exact id (Int.ModEq.symm hν)
    have hν : ↑N ∣ (2 ^ (2 * α) - 1 : ℤ) := by
      apply Int.dvd_of_dvd_mul_left_of_gcd_one hν
      norm_cast
      apply Nat.coprime_iff_gcd_eq_one.mp
      apply Nat.Coprime.pow_right
      simp [μ]
      apply Nat.Coprime.prod_right
      intro i _
      apply Nat.Prime.coprime_iff_not_dvd hN |>.mpr
      intro h
      apply Nat.le_of_dvd (hm_pos _) at h
      simp [←hmn i, n] at h
      obtain h' := hn_gt_m i
      simp [h] at h'
    have hν : N ∣ 2 ^ (2 * α) - 1 := by
      suffices : (N : ℤ) ∣ (2 ^ (2 * α) - 1 : ℕ)
      · exact Int.ofNat_dvd.mp this
      · rw [Nat.cast_sub]
        · simp [hν]
        · exact Nat.one_le_two_pow
    -- Since ∀ k ∈ Icc 1 (N - 2), ¬ N ∣ 2 ^ k - 1, we have 2 * α ≥ N - 1.
    have hα : 2 * α ≥ N - 1 := by
      by_contra hα
      simp at hα
      have hα : 2 * α ∈ Icc 1 (N - 2) := by
        simp
        constructor
        · by_contra h
          simp [α] at h
          obtain h := h 0 ht
          have : a 0 > 0 := by
            obtain ⟨m, hm⟩ := heven_n 0
            ring_nf at hm
            simp at hm
            simp [a, n, hm]
            rw [Nat.factorization_mul]
            · simp
              right
              rw [Nat.Prime.factorization]
              · simp
              · norm_num
            . intro h; simp [h] at hm; obtain h' := hn_gt_m 0; simp [hm] at h'
            · simp
          simp [h] at this
        · exact Nat.le_sub_of_add_le hα
      apply hndvd at hα
      contradiction
    -- Now, we prove that 2 * α < N - 1, where is a contradiction.
    have : ¬ 2 * α ≥ N - 1 := by
      simp
      -- First, note that (range t).image n ⊆ (Ioc (N / 2) N).filter Even 
      have himg : (range t).image n ⊆ (Ioc (N / 2) N).filter Even := by
        intro x hx
        simp at hx ⊢
        obtain ⟨a, _, ha⟩ := hx
        simp [←ha, heven_n]
        constructor
        · by_contra h
          simp at h
          have : m a + n a < N := by
            apply lt_of_lt_of_le (b := n a + n a)
            · simp [hn_gt_m a]
            · ring_nf
              exact Nat.mul_le_of_le_div 2 (n a) N h
          simp [←hmn a] at this
        · simp [←hmn a]
      -- and n is injective on (range t).
      have hinjOn : Set.InjOn n ↑(range t) := by
        intro x hx y hy h
        have : f^[x] s = f^[y] s := by
          apply Prod.ext
          · have : m x + n x = m y + n y := by rw [hmn, hmn]
            simp [h] at this
            exact this
          · exact h
        wlog hxy : x < y generalizing x y with H
        · simp at hxy
          rcases lt_or_eq_of_le hxy with hxy | hxy
          · obtain H := H hy hx (by exact id (Eq.symm h)) (by simp [this]) hxy
            simp [H]
          · simp [hxy]
        · have : f^[y - x] s = s := by exact f_cancel hS hf hs this
          have hle : t ≤ y - x := by
            apply hle
            simp [P, this, hxy]
          simp at hy
          have : ¬ y < t := by
            simp
            apply le_trans hle
            simp
          contradiction
      -- Now, we can find n₀ ∈ ((Ioc (N / 2) N).filter Even) \ (range t).image n since 
      -- #((Ioc (N / 2) N).filter Even) = (N - 1) / 4 > t = #(range t).
      have ⟨n₀, hn₀⟩ : (((Ioc (N / 2) N).filter Even) \ (range t).image n).Nonempty := by
        refine sdiff_nonempty.mpr ?_
        intro h
        apply subset_antisymm himg at h
        apply congrArg card at h
        rw [card_image_of_injOn, card_even hodd_N] at h
        · simp at h
          simp [h] at hlt
        · exact hinjOn
      -- Therefore, we have ν = ∏ i ∈ range t, n i ∣ (((Ioc (N / 2) N).filter Even).erase n₀).prod id.
      have hν : ν = (image n (range t)).prod id := by
        rw [prod_image]
        · simp
        · apply hinjOn
      have hν_dvd : ν ∣ (((Ioc (N / 2) N).filter Even).erase n₀).prod id := by
        rw [hν]
        apply prod_dvd_prod_of_subset
        intro x hx
        refine mem_erase_of_ne_of_mem ?_ (himg hx)
        intro h
        simp only [←h, mem_sdiff, hx] at hn₀
        simp at hn₀
      -- Then, padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) ≥ padicValNat 2 ν = padicValNat 2 (2 ^ α * μ) = α.
      have hpadic : padicValNat 2 ν ≤ padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) := by
        apply padic_le_of_dvd hν_dvd
        simp
        by_contra h
        obtain ⟨a, ha, ha_eq_zero⟩ := prod_eq_zero_iff.mp h
        simp [ha_eq_zero] at ha
      have hpadic_μ : padicValNat 2 μ = 0 := by
        simp; right
        by_contra h
        simp [μ] at h
        apply Nat.dvd_of_mod_eq_zero at h
        apply Prime.dvd_finset_prod_iff (by refine Nat.prime_iff.mp ?_; norm_num)  _ |>.mp at h
        obtain ⟨a, ha, hdvd⟩ := h
        have : Even (m a) := by exact (even_iff_exists_two_nsmul (m a)).mpr hdvd
        have : ¬ Even (m a) := by
          simp
          apply odd_of_coprime_even (heven_n a) (hco_mn a)
        contradiction
      have hpadic_ν : padicValNat 2 ν = α := by
        rw [hμ, padicValNat.mul, padicValNat.pow]
        · simp [hpadic_μ]
        · simp
        · positivity
        · positivity
      -- We have proved that padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) < N - 1 / 2.
      have hpadic_prod : padicValNat 2 ((((Ioc (N / 2) N).filter Even).erase n₀).prod id) < (N - 1) / 2 := by
        apply padic_prod_erase
        · simp only [mem_sdiff] at hn₀
          exact hn₀.1
        · exact hodd_N
      -- Hence, we have α < (N - 1) / 2.
      apply lt_of_le_of_lt hpadic at hpadic_prod
      rw [hpadic_ν] at hpadic_prod
      -- i.e., we have 2 * α < N - 1, which is a contradiction.
      have : 2 * α < N - 1 := by
        apply lt_of_lt_of_le (b := 2 * ((N - 1) / 2))
        · gcongr
        · exact Nat.mul_div_le (N - 1) 2
      exact Nat.add_lt_of_lt_sub this
    contradiction

/- 13. (IRE 3) Let $S$ be the set of all pairs $(m, n)$ of relatively prime positive integers $m, n$ with $n$ even and $m< n$. For $s=(m, n) \in S$ write $n=2^{k} n_{0}$, where $k, n_{0}$ are positive integers with $n_{0}$ odd and define $f(s)=\left(n_{0}, m+\right.$ $n-n_{0}$ ). Prove that $f$ is a function from $S$ to $S$ and that for each $s=(m, n) \in S$, there exists a positive integer $t \leq \frac{m+n+1}{4}$ such that $f^{t}(s)=s$, where  $$ f^{t}(s)=\underbrace{(f \circ f \circ \cdots \circ f)}_{t \text { times }}(s) . $$  If $m+n$ is a prime number that does not divide $2^{k}-1$ for $k=1,2, \ldots, m+$ $n-2$, prove that the smallest value of $t$ that satisfies the above conditions is $\left[\frac{m+n+1}{4}\right]$, where $[x]$ denotes the greatest integer less than or equal to $x$. -/
theorem number_theory_24463 {f : ℕ × ℕ → ℕ × ℕ} {S : Set (ℕ × ℕ)} (hS : S = {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n})
    (hf : ∀ m n, f (m, n) = (n / 2 ^ (Nat.factorization n 2), m + n - n / 2 ^ (Nat.factorization n 2))) :
    (∀ s ∈ S, f s ∈ S) ∧
    (∀ m n, (m, n) ∈ S → ∃ t, t > 0 ∧ t ≤ (m + n + 1) / 4 ∧ f^[t] (m, n) = (m, n)) ∧
    (∀ m n, (m, n) ∈ S → Nat.Prime (m + n) → (∀ k ∈ Icc 1 (m + n - 2), ¬ (m + n) ∣ 2 ^ k - 1) → IsLeast {t | t > 0 ∧ f^[t] (m, n) = (m, n)} ((m + n + 1) / 4)) := by
  -- Define the set SN as the set of pairs (m, n) such that m > 0, m < n, n is even, m and n are coprime, and m + n = N for some x in S.
  let SN (x : ℕ × ℕ) := {(m, n) : ℕ × ℕ | m > 0 ∧ m < n ∧ Even n ∧ m.Coprime n ∧ m + n = x.1 + x.2}
  have hmem {x : ℕ × ℕ} (hx : x ∈ S) : x ∈ SN x := by
    simp [SN]
    simp [hS] at hx
    exact hx
  split_ands
  · -- If x ∈ S, then x ∈ SN for some N.
    -- We prove that f maps SN to SN.
    -- So f x ∈ SN ⊆ S.
    intro x hs
    have : f x ∈ SN x := by apply mapsTo_f_SN_SN rfl hf (hmem hs)
    simp [SN] at this
    simp [hS, this]
    exact this.2.2.2.1
  · -- For each x ∈ S, we prove that there exists a positive integer t such that f^[t] x = x and t ≤ (m + n + 1) / 4 by lemma exists_nth_apply_eq.
    intro m n hs
    exact exists_nth_apply_eq rfl hf (m, n) (hmem hs)
  · -- For each x ∈ S, assume that N is a prime dividing m + n, and ∀ k ∈ Icc 1 (m + n - 2), ¬ N ∣ 2 ^ k - 1.
    intro m n hs hprime hndvd
    -- By lemma le_of_nth_apply_eq, we prove that ∀ (t : ℕ), t > 0 ∧ f^[t] (m, n) = (m, n) → t ≥ (m + n + 1) / 4
    obtain h := le_of_nth_apply_eq rfl hf hprime hndvd (m, n) (hmem hs)
    constructor
    · simp
      -- We know that there exists t such that f^[t] (m, n) = (m, n) and t ≤ (m + n + 1) / 4.
      -- Then by the lemma, we have t ≥ (m + n + 1) / 4, i.e., t = (m + n + 1) / 4.
      obtain ⟨t, ht, hle, heq⟩ := exists_nth_apply_eq rfl hf (m, n) (hmem hs)
      have : t = (m + n + 1) / 4 := by
        apply le_antisymm hle
        apply h t ⟨ht, heq⟩
      simp [←this, heq]
      apply lt_of_lt_of_le ht at hle
      simp at hle
      exact hle
    · -- If r > 0 and f^[r] (m, n) = (m, n), then t ≥ (m + n + 1) / 4.
      intro r hr
      simp at hr
      exact h r hr
