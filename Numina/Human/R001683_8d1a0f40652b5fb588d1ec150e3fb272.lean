import Mathlib

open Finset


/- Since d i < d (i + 1), we can prove by induction that d is monotone. -/
lemma mono_of_lt {k : ℕ} {d : ℕ → ℕ} (hd : ∀ i ∈ Ico 1 k , d i < d (i + 1)) : StrictMonoOn d (Icc 1 k) := by
  intro i hi j hj hij
  simp at hi hj
  induction j, hij using Nat.le_induction
  · apply hd
    simp
    constructor
    · exact hi.1
    · obtain h := hj.2
      exact h
  · rename_i j hj ih
    trans d j
    · apply ih
      constructor
      · trans i + 1
        · trans i
          · exact hi.1
          · simp
        · assumption
      · trans j + 1
        · simp
        · exact hj.2
    · apply hd
      simp
      constructor
      · trans i + 1
        · trans i
          · exact hi.1
          · simp
        · assumption
      · obtain h := hj.2
        exact h

/- Note that d 1 = 1 > 0, therefore, d i > 0. -/
lemma pos_of_mono {k : ℕ} {d : ℕ → ℕ} (hd : ∀ i ∈ Ico 1 k , d i < d (i + 1)) (hd₁ : d 1 = 1) : ∀ i ∈ Icc 1 k, d i > 0 := by
  obtain hstrict_mono := mono_of_lt hd
  obtain hmono : MonotoneOn d (Icc 1 k) := by
    exact StrictMonoOn.monotoneOn hstrict_mono
  intro i hi
  simp at hi
  apply lt_of_lt_of_le (b := d 1)
  · simp [hd₁]
  · apply hmono
    · simp
      apply le_trans hi.1 hi.2
    · simp
      exact hi
    · exact hi.1

/- We prove that d i * d (k + 1 - i) = n -/
lemma mul_eq_n {n : ℕ} (hn : n ≠ 0) {d : ℕ → ℕ} (hdivisors : (Icc 1 k).image d = n.divisors)
    (hd : ∀ i ∈ Ico 1 k , d i < d (i + 1)) (hd₁ : d 1 = 1) (hdk : d k = n) :
    ∀ i ∈ Icc 1 k, d i * d (k + 1 - i) = n := by
  obtain hstrict_mono := mono_of_lt hd
  obtain hmono : MonotoneOn d (Icc 1 k) := by
    exact StrictMonoOn.monotoneOn hstrict_mono
  have hpos : ∀ i ∈ Icc 1 k, d i > 0 := by apply pos_of_mono hd hd₁
  intro i hi
  simp at hi
  obtain ⟨h₁, h₂⟩ := hi
  -- We prove by induction on i.
  induction i, h₁ using Nat.le_induction
  · simp [hd₁, hdk]
  · rename_i i h₁ ih
    have h₁ : d (i + 1) ∈ n.divisors := by
      rw [←hdivisors]
      simp
      use i + 1
      simp [h₂]
    -- assume that n = d (i + 1) * x since d (i + 1) ∈ n.divisors.
    have ⟨x, hx⟩ : d (i + 1) ∣ n := by exact Nat.dvd_of_mem_divisors h₁
    have h₂ : x ∈ (Icc 1 k).image d := by
      rw [hdivisors]
      simp [hn]
      use d (i + 1)
      rw [hx]
      ring
    simp at h₂
    -- wlog, we assume that d j = x
    obtain ⟨j, hj_mem, hj⟩ := h₂
    rw [←hj] at hx
    rw [hx]
    congr
    -- We need to prove that j = k - i
    have hi : i ≤ k := by
      apply le_trans ?_ h₂
      simp
    obtain ih := ih hi
    simp
    by_contra h
    -- Otherwise, we have j < k - i ∨ j > k - i
    rcases lt_or_gt_of_ne h with hlt | hgt
    · -- If k - i < j, then we have n = d i * d (k + 1 - i) < d (i + 1) * d j = n, which is a contradiction.
      have h₁ : k + 1 - i ≤ j := by
        rw [Nat.sub_add_comm]
        exact hlt
        apply le_trans ?_ h₂
        simp
      have h₂ : d (k + 1 - i) ≤ d j := by
        apply hmono
        · simp
          constructor
          · trans (i + 1) + 1 - i
            · rw [add_assoc, Nat.add_sub_cancel_left]
              simp
            · gcongr
          · assumption
        · simp
          exact hj_mem
        · exact h₁
      have h₃ : d i * d (k + 1 - i) < d (i + 1) * d j := by
        apply Nat.mul_lt_mul_of_lt_of_le
        · apply hd
          simp
          constructor
          · assumption
          · assumption
        · exact h₂
        · apply hpos
          simp [hj_mem]
      simp [ih, ←hx] at h₃
    · -- If j < k - i, then j < j + 1 ≤ k - i
      have h₁ : d (j + 1) ∈ n.divisors := by
        rw [←hdivisors]
        simp
        use j + 1
        simp
        trans k - i
        · exact hgt
        · simp
      -- wlog, we assume that d (j + 1) * d a = n
      have ⟨y, hy⟩ : d (j + 1) ∣ n := by exact Nat.dvd_of_mem_divisors h₁
      have h₂ : y ∈ (Icc 1 k).image d := by
        rw [hdivisors]
        simp [hn]
        use d (j + 1)
        rw [hy]
        ring
      simp at h₂
      obtain ⟨a, ha_mem, ha⟩ := h₂
      -- Then we have d i < d a < d (j + 1)
      have h₃ : d a > d i := by
        by_contra h₃
        simp at h₃
        have : d (j + 1) < d (k + 1 - i) := by
          apply hstrict_mono
          · simp
            trans k - i
            · exact hgt
            · simp
          · simp
            constructor
            · trans (i + 1) + 1 - i
              · rw [add_assoc, Nat.add_sub_cancel_left]
                simp
              · gcongr
            · assumption
          · apply lt_of_lt_of_eq (b := k - i + 1)
            · gcongr
            · rw [Nat.sub_add_comm]
              exact hi
        have : d a * d (j + 1) < d i * d (k + 1 - i) := by
          apply Nat.mul_lt_mul_of_le_of_lt
          · exact h₃
          · exact this
          · apply hpos
            simp
            constructor
            · assumption
            · exact hi
        simp [ih, hy, ha, mul_comm] at this
      have h₄ : d a < d (i + 1) := by
        by_contra h₄
        simp at h₄
        have : d (j + 1) > d j := by
          apply hd
          simp
          constructor
          · exact hj_mem.1
          · apply lt_of_lt_of_le hgt
            simp
        have : d a * d (j + 1) > d (i + 1) * d j := by
          apply Nat.mul_lt_mul_of_le_of_lt
          · exact h₄
          · exact this
          · apply hpos
            simp
            exact ha_mem
        simp [←hx, ha, mul_comm, hy] at this
      -- Note that d is strictly monotone, so we have i < a < i + 1, which is impossible.
      have h₅ : a > i := by
        apply StrictMonoOn.lt_iff_lt hstrict_mono  ?_ ?_ |>.mp h₃
        · simp
          constructor
          · assumption
          · exact hi
        · simp
          exact ha_mem
      have h₆ : a < i + 1 := by
        apply StrictMonoOn.lt_iff_lt hstrict_mono ?_ ?_ |>.mp h₄
        · simp
          exact ha_mem
        · simp
          exact h₂
      linarith only [h₅, h₆]

/- (∑ i in Ico 1 k, d i * d (i + 1)) / (n ^ 2 : ℝ) = ∑ i ∈ Ico 1 k, (1 : ℝ) / (d (k + 1 - i) * d (k - i)) -/
lemma div_eq_sum_inv_mul {n : ℕ} (hn : n ≠ 0) {d : ℕ → ℕ} (hdivisors : (Icc 1 k).image d = n.divisors)
    (hd : ∀ i ∈ Ico 1 k , d i < d (i + 1)) (hd₁ : d 1 = 1) (hdk : d k = n) :
    (∑ i in Ico 1 k, d i * d (i + 1)) / (n ^ 2 : ℝ) = ∑ i ∈ Ico 1 k, (1 : ℝ) / (d (k + 1 - i) * d (k - i)) := by
  simp
  rw [sum_div]
  apply sum_congr rfl
  intro x hx
  rw [sq]
  field_simp
  obtain h₁ : d x * d (k + 1 - x) = n := by
    apply mul_eq_n hn hdivisors hd hd₁ hdk x
    simp at hx ⊢
    constructor
    · exact hx.1
    · exact le_of_lt hx.2
  obtain h₂ : d (x + 1) * d (k + 1 - (x + 1)) = n := by
    apply mul_eq_n hn hdivisors hd hd₁ hdk (x + 1)
    simp at hx ⊢
    exact hx.2
  nth_rw 1 [←h₁, ←h₂]
  have h₃ : d (k + 1 - x) > 0 := by
    apply pos_of_mono hd hd₁
    simp
    constructor
    · simp at hx
      trans (x + 1) + 1 - x
      · rw [add_assoc, Nat.add_sub_cancel_left]
        simp
      · gcongr
        exact hx.2
    · simp at hx
      exact hx.1
  have h₄ : d (k - x) > 0 := by
    apply pos_of_mono hd hd₁
    simp
    simp at hx
    trans x + 1 - x
    · simp
    · gcongr
      exact hx.2
  field_simp
  ring_nf
  simp [mul_assoc]
  left; left
  rw [mul_comm]
  congr 3
  rw [←Nat.sub_sub, Nat.add_sub_cancel_left]


/- 2. N2 (ROM) ${ }^{\mathrm{IMO} 4}$ Let $n \geq 2$ be a positive integer, with divisors $1=d_{1}<$ $d_{2}<\cdots < d_{k}=n$.
 Prove that $d_{1} d_{2}+d_{2} d_{3}+\cdots+d_{k-1} d_{k}$ is always less than $n^{2}$, and determine when it is a divisor of $n^{2}$. -/
theorem number_theory_25119 {n k : ℕ} (hn : 2 ≤ n) {d : ℕ → ℕ} (hdivisors : (Icc 1 k).image d = n.divisors)
    (hd : ∀ i ∈ Ico 1 k , d i < d (i + 1)) (hd₁ : d 1 = 1) (hdk : d k = n) :
    ∑ i ∈ Ico 1 k, d i * d (i + 1) < n ^ 2 ∧
    (∑ i ∈ Ico 1 k, d i * d (i + 1) ∣ n ^ 2 ↔ Nat.Prime n) := by

  -- Note that k > 1 must hold, since n ≥ 2 and d 1 = 1.
  have hk : k > 1 := by
    by_contra h
    simp at h
    interval_cases k
    · simp at hdivisors
      rw [eq_comm] at hdivisors
      apply Nat.divisors_eq_empty.mp at hdivisors
      simp [hdivisors] at hn
    · rw [hd₁] at hdk
      simp [←hdk] at hn

  -- We first show that the sum (denoted by S) is less than n^2 by showing S / n ^ 2 < 1.
  have h₁ : (∑ i in Ico 1 k, d i * d (i + 1)) / (n ^ 2 : ℝ) < 1 := by
    -- We have prove that S / n ^ 2 = ∑ i ∈ Ico 1 k, (1 : ℝ) / (d (k + 1 - i) * d (k - i)).
    rw [div_eq_sum_inv_mul (by exact Nat.not_eq_zero_of_lt hn) hdivisors hd hd₁ hdk]
    apply lt_of_le_of_lt (b := 1 - (1 : ℝ) / d k)
    · -- Therefore S / n ^ 2 < ∑ i, ((1 / d (k - i) - (1 / d (k + 1 - i)).
      trans ∑ i ∈ Ico 1 k, (1 / ↑(d (k - i)) - 1 / ↑(d (k + 1 - i)))
      · apply sum_le_sum
        intro i hi
        apply sub_nonneg.mp
        have : d (k + 1 - i) > 0 := by
          apply pos_of_mono hd hd₁
          simp at hi ⊢
          constructor
          · trans i + 1 + 1 - i
            · rw [add_assoc, Nat.add_sub_cancel_left]
              simp
            · gcongr
              exact hi.2
          · exact hi.1
        have : d (k - i) > 0 := by
          apply pos_of_mono hd hd₁
          simp at hi ⊢
          trans i + 1 - i
          · simp
          · gcongr
            exact hi.2
        field_simp
        apply div_nonneg
        · trans (↑(d (k + 1 - i)) - ↑(d (k - i)) - 1) * (↑(d (k + 1 - i)) * ↑(d (k - i)))
          · apply mul_nonneg
            · simp
              norm_cast
              suffices : 0 < Int.subNatNat (d (k + 1 - i)) (d (k - i))
              · exact this
              · rw [Int.subNatNat_eq_coe]
                simp
                have : k + 1 - i = k - i + 1 := by
                  rw [Nat.sub_add_comm]
                  simp at hi
                  exact le_of_lt hi.2
                rw [this]
                apply hd
                simp
                simp at hi
                split_ands
                · trans i + 1 - i
                  · simp
                  · gcongr
                    exact hi.2
                · obtain h := hi.2
                  exact Nat.zero_lt_of_lt h
                · exact hi.1
            · positivity
          · apply le_of_eq
            ring
        · positivity
      · -- = 1 - 1 / d k < 1
        rw [sum_sub_distrib]
        have : Ico 1 k = Ioo  1 k ∪ {1} := by
          ext i
          simp
          constructor <;> intro h
          · by_cases hi : i = 1
            · simp [hi]
            · left
              constructor
              · apply lt_of_le_of_ne
                · exact h.1
                · exact fun a ↦ hi (id (Eq.symm a))
              · exact h.2
          · rcases h with h | h
            · simp [h]
              apply le_of_lt h.1
            · simp [h]
              exact hk
        nth_rw 2 [this]
        have : Ico 1 k = Ioo 0 (k - 1) ∪ {k - 1} := by
          ext i
          simp
          constructor <;> intro h
          · by_cases hi : i = k - 1
            · simp [hi]
            · left
              constructor
              · exact h.1
              · apply lt_of_le_of_ne
                · apply Nat.le_sub_of_add_le
                  exact h.2
                · exact hi
          · rcases h with h | h
            · constructor
              · exact h.1
              · apply lt_of_lt_of_le h.2
                simp
            · simp [h]
              constructor
              · apply Nat.le_sub_of_add_le
                exact hk
              · exact Nat.zero_lt_of_lt hk
        nth_rw 1 [this, sum_union, sum_union]
        · simp
          rw [Nat.sub_sub_self, hd₁]
          simp
          · apply le_of_eq
            ring_nf
            simp
            have : (Ioo 0 (k - 1)).image (fun i => i + 1) = Ioo 1 k := by
              ext i
              simp
              rw [Nat.sub_add_cancel]
              tauto
              exact Nat.one_le_of_lt hk
            rw [←this, sum_image]
            · congr
              ext i
              simp
              congr 1
              rw [add_comm i, ←Nat.sub_sub, Nat.add_sub_cancel_left]
            · intro x _  y _ h
              exact Nat.succ_inj'.mp h
          · exact Nat.one_le_of_lt hk
        · simp
        · simp
    · simp
      apply pos_of_mono hd hd₁
      simp
      exact Nat.one_le_of_lt hk

  constructor
  · -- Since S / n ^ 2 < 1, we have S < n ^ 2.
    apply sub_pos.mpr at h₁
    field_simp at h₁
    norm_cast at h₁
  · constructor
    · -- If S ∣ n ^ 2, then ∃ x such that S * x = n ^ 2
      intro h
      obtain ⟨x, hx⟩ := h
      have : ∑ i ∈ Ico 1 k, d i * d (i + 1) ≥ d (k - 1) * d k := by
        trans ∑ i ∈ {k - 1}, d i * d (i + 1)
        · apply sum_le_sum_of_subset
          · simp
            constructor
            · apply Nat.le_sub_of_add_le
              exact hk
            · exact Nat.zero_lt_of_lt hk
        · simp
          apply le_of_eq
          congr
          rw [Nat.sub_add_cancel]
          exact Nat.one_le_of_lt hk
      simp [hdk] at this
      -- However, since S ≥ n * d (k - 1), we have n ≥ d (k - 1) * x.
      have hge : n ^ 2 ≥ n * d (k - 1) * x := by
        rw [hx]
        apply mul_le_mul_of_nonneg_right
        · rw [mul_comm]
          apply le_trans this
          apply le_of_eq
          rfl
        · simp
      -- Note that n = d (k - 1) * d 2, so x ≤ d 2
      obtain h : d 2 * d (k - 1) = n := by
        apply mul_eq_n
        · exact Nat.not_eq_zero_of_lt hn
        · exact hdivisors
        · exact hd
        · exact hd₁
        · exact hdk
        · simp
          exact hk
      rw [sq] at hge
      nth_rw 2 [←h] at hge
      rw [mul_comm (d 2), ←mul_assoc] at hge
      have hle : x ≤ d 2 := by
        apply le_of_mul_le_mul_left hge
        simp
        constructor
        · exact Nat.zero_lt_of_lt hn
        · apply pos_of_mono hd hd₁
          simp
          apply Nat.le_sub_of_add_le
          exact hk
      -- We verify that x ≠ 1, so x ≠ d 1
      by_cases heq : x = 1
      · simp [heq] at hx
        apply sub_pos.mpr at h₁
        field_simp at h₁
        norm_cast at h₁
        simp [hx] at h₁
      · -- For any prime p ∣ x, then p ∣ n ^ 2 and p ∣ n.
        -- Since p ≤ x ≤ d 2, we must have p = d 2.
        apply lt_or_gt_of_ne at heq
        simp at heq
        rcases heq with heq | heq
        · simp [heq] at hx
          simp [hx] at hn
        · obtain ⟨p, hp, hdvd⟩ : ∃ p, Nat.Prime p ∧ p ∣ x := by
            apply Nat.exists_prime_and_dvd
            exact Ne.symm (Nat.ne_of_lt heq)
          have : p ∣ n ^ 2 := by
            rw [hx]
            exact Dvd.dvd.mul_left hdvd (∑ i ∈ Ico 1 k, d i * d (i + 1))
          have : p ∣ n := by
            exact Nat.Prime.dvd_of_dvd_pow hp this
          have : p ∈ n.divisors := by
            refine Nat.mem_divisors.mpr ?_
            simp [this]
            exact Nat.not_eq_zero_of_lt hn
          simp [←hdivisors] at this
          obtain ⟨i, hi, hdi⟩ := this
          have : d i ≤ d 2 := by
            rw [hdi]
            apply le_trans ?_ hle
            apply Nat.le_of_dvd ?_ hdvd
            exact Nat.zero_lt_of_lt heq
          have : i ≤ 2 := by
            obtain hmono := mono_of_lt hd
            apply StrictMonoOn.le_iff_le hmono ?_ ?_ |>.mp this
            · simp
              exact hi
            · simp
              exact hk
          obtain hi := hi.1
          interval_cases i
          · simp [hd₁] at hdi
            simp [←hdi] at hp
            norm_num at hp
          · -- Hence, S = d (k - 1) * n
            -- We claim that k = 2, otherwise S > d (k - 1) * n
            have heq : x = d 2 := by
              apply le_antisymm hle
              rw [hdi]
              apply Nat.le_of_dvd ?_ hdvd
              exact Nat.zero_lt_of_lt heq
            rw [heq] at hx
            nth_rw 1 [sq, ←h, mul_comm _ (d 2), mul_assoc] at hx
            simp at hx
            rcases hx with hx | hx
            · rw [←hdk] at hx
              have : k = 2 := by
                by_contra h
                have hk : k > 2 := by
                  exact Nat.lt_of_le_of_ne hk fun a ↦ h (id (Eq.symm a))
                have : d (k - 1) * d k < ∑ i ∈ Ico 1 k, d i * d (i + 1) := by
                  apply lt_of_eq_of_lt (b := ∑ i ∈ {k - 1}, d i * d (i + 1))
                  · simp
                    left
                    rw [Nat.sub_add_cancel]
                    exact Nat.one_le_of_lt hk
                  · apply sum_lt_sum_of_subset (i := 1)
                    · simp
                      assumption
                    · simp
                      by_contra h'
                      have : k = 1 + 1 := by
                        nth_rw 1 [h']
                        rw [Nat.sub_add_cancel]
                        exact Nat.one_le_of_lt hk
                      simp [this] at h
                    · apply mul_pos
                      · apply pos_of_mono hd hd₁
                        simp
                        exact Nat.zero_lt_of_lt hk
                      · apply pos_of_mono hd hd₁
                        simp
                        assumption
                    · simp
                    · simp
                      constructor
                      · apply Nat.le_sub_of_add_le
                        assumption
                      · exact Nat.zero_lt_of_lt hk
                simp [hx] at this
              -- Now n = d 2 = p is a prime.
              rw [←this] at hdi
              rw [hdk] at hdi
              rw [←hdi] at hp
              exact hp
            · simp [hx] at hdi
              simp [←hdi] at hp
              norm_num at hp
    · -- If n is a prime, then k = 2
      intro h
      have : k = 2 := by
        by_contra h'
        have hk : k > 2 := by
          exact Nat.lt_of_le_of_ne hk fun a ↦ h' (id (Eq.symm a))
        have h₁ : d 2 < d k := by
          obtain hmono := mono_of_lt hd
          apply StrictMonoOn.lt_iff_lt hmono ?_ ?_ |>.mpr
          · exact hk
          · simp
            assumption
          · simp
            exact Nat.one_le_of_lt hk
        have h₂ : d 2 > d 1 := by
          apply hd
          simp
          assumption
        have : d 2 ∈ n.divisors := by
          rw [←hdivisors]
          simp
          use 2
          simp
          apply le_of_lt hk
        simp at this
        obtain hdvd := this.1
        apply Nat.dvd_prime h |>.mp at hdvd
        rcases hdvd with h | h
        · simp [h, hd₁] at h₂
        · simp [h, hdk] at h₁
      -- S = d 1 * d 2 = n ∣ n ^ 2
      simp [this] at hdk ⊢
      simp [hdk, hd₁]
      exact Dvd.intro_left (n.pow 1) rfl
