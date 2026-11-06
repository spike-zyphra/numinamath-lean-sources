import Mathlib

/- Find the number of positive integers $n$ less than $1000$ for which there exists a positive real number $x$ such that $n=x\lfloor x \rfloor$.
Note: $\lfloor x \rfloor$ is the greatest integer less than or equal to $x$. -/
theorem number_theory_95248 :
    {n : ℕ | 0 < n ∧ n < 1000 ∧ ∃ x : ℝ, 0 < x ∧ x * ⌊x⌋ = n}.ncard = 496 := by

  let f : ℝ → ℝ := fun x => x * ⌊x⌋

  -- First we observe that if x ∈ [k, k + 1), ⌊x⌋ = k so f x = k * x, and maps this
  -- range onto [k^2, k^2 + k).
  have hfimage {k : ℕ} (hk : 0 < k) : f '' Set.Ico k (k + 1) = Set.Ico (k ^ 2 : ℝ) (k ^ 2 + k : ℝ) := by
    ext y
    simp [f]
    constructor
    . rintro ⟨x, ⟨⟨hxl, hxr⟩, hx⟩⟩
      have : ⌊x⌋ < k + 1 := Int.floor_lt.mpr (by simpa)
      have : k ≤ ⌊x⌋ := Int.le_floor.mpr (by simpa)
      have : ⌊x⌋ = k := by linarith
      rw [this] at hx
      norm_cast at hx
      rw [← hx]
      and_intros
      . nlinarith
      . rw [show (k ^ 2 + k : ℝ) = (k + 1) * k by ring]
        rw [mul_lt_mul_right (by simpa)]
        exact hxr
    . intro ⟨hkl, hkr⟩
      use y / k
      have : k ≤ y / k := by
        rw [le_div_iff₀ (by simpa), ← pow_two]
        exact hkl
      have : y / k < k + 1 := by
        rw [div_lt_iff₀ (by simpa), add_mul, ← pow_two, one_mul]
        exact hkr
      and_intros
      . assumption
      . assumption
      . have : ⌊y / k⌋ < k + 1 := Int.floor_lt.mpr (by simpa)
        have : k ≤ ⌊y / k⌋ := Int.le_floor.mpr (by simpa)
        have : ⌊y / k⌋ = k := by linarith
        rw [this]
        simp [show k ≠ 0 by linarith]

  -- We see that if n ∈ [k^2, k^2 + k) then 1 ≤ n < 1000 exactly when 1 ≤ k < 32. Thus, we can write a bijection between the finite set of pairs
  -- (k, n) such that k < 32 and n ∈ [k^2, k^2 + k), and our target set.
  let e : Finset.sigma (Finset.Ico 1 32) (fun k => Finset.Ico (k ^ 2) (k ^ 2 + k)) ≃ { n : ℕ | 0 < n ∧ n < 1000 ∧ ∃ x, 0 < x ∧ f x = n } :=
    { toFun := fun ⟨⟨k, n⟩, h⟩ => ⟨n, by
        simp
        simp at h
        rcases h with ⟨⟨hkl, hkr⟩, _, _⟩
        and_intros
        . nlinarith
        . nlinarith
        . have : ↑n ∈ Set.Ico (k ^ 2 : ℝ) (k ^ 2 + k : ℝ) := by simp; norm_cast
          rw [← hfimage (by simpa)] at this
          simp at this
          obtain ⟨x, ⟨⟨_, _⟩, hx⟩⟩ := this
          have hxpos : 0 < x := by rify at hkl; linarith
          exact ⟨x, ⟨hxpos, hx⟩⟩⟩
      invFun := fun ⟨n, h⟩ => ⟨⟨Nat.sqrt n, n⟩, by
        simp
        simp at h
        rcases h with ⟨hl, hr, ⟨x, ⟨_, hx⟩⟩⟩
        set k := Nat.sqrt n with hk
        have : k ^ 2 ≤ n := Nat.sqrt_le' _
        have : n < (k + 1) ^ 2 := Nat.lt_succ_sqrt' _
        -- From f x = n, we have a unique k' such that x ∈ [k', k' + 1).
        -- From the bounds on n, we know that k = k'.
        let k' : ℕ := ⌊x⌋.natAbs
        have hk' : (k' : ℝ) = ⌊x⌋ := by
          simp [k']
          suffices : ⌊x⌋.natAbs = ⌊x⌋
          . nth_rw 2 [← this]; rfl
          apply Int.natAbs_of_nonneg
          rw [Int.floor_nonneg]
          linarith
        have : k' > 0 := by
          rcases Nat.eq_zero_or_pos k' with (h | h)
          . exfalso
            simp [f] at hx
            rw [← hk', h] at hx
            simp at hx
            norm_cast at hx
            linarith
          . exact h
        have : f x ∈ f '' Set.Ico (k' : ℝ) (k' + 1 : ℝ) := by
          apply Set.mem_image_of_mem
          simp
          rw [hk']
          and_intros
          . exact Int.floor_le _
          . exact Int.lt_floor_add_one _
        rw [hfimage (by assumption), hx] at this
        simp at this
        obtain ⟨hl, hr⟩ := this
        norm_cast at hl hr
        have hkunique (k1 k2 : ℕ) (hk1 : k1 ^ 2 ≤ n ∧ n < (k1 + 1) ^ 2) (hk2 : k2 ^ 2 ≤ n ∧ n < (k2 + 1) ^ 2) : k1 = k2 := by
          rcases hk1 with ⟨hkl1, hkr1⟩
          rcases hk2 with ⟨hkl2, hkr2⟩
          rcases lt_trichotomy k1 k2 with (h | h | h)
          . exfalso
            have : (k1 + 1) ^ 2 ≤ k2 ^ 2 := by nlinarith
            linarith
          . exact h
          . exfalso
            have : (k2 + 1) ^ 2 ≤ k1 ^ 2 := by nlinarith
            linarith
        have : k' = k := hkunique k' k ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
        rw [this] at hl hr
        and_intros
        . nlinarith
        . nlinarith
        . exact hl
        . exact hr⟩
      left_inv := fun ⟨⟨k, n⟩, h⟩ => by
        simp
        simp at h
        rcases h with ⟨_, hkl, hkr⟩
        have : Nat.sqrt n < k + 1 := Nat.sqrt_lt'.mpr (show n < (k + 1) ^ 2 by linarith)
        have : k ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hkl
        linarith
      right_inv := fun ⟨n, _⟩ => by simp
    }

  -- Finally, we use this equivalence to compute the cardinality.
  simp only [f] at e
  rw [←Set.Nat.card_coe_set_eq, ← Nat.card_congr e, Nat.card_eq_finsetCard, Finset.card_sigma]
  -- Each inner [k ^ 2, k ^ 2 + k) interval has cardinality k, so the whole sum
  -- is the 0 + 1 + ... + 31 = 32 * (32 - 1) / 2 = 496.
  simp
  suffices : Finset.sum (Finset.range 32) (fun k => k) = 496
  . rw [← this, ← Finset.sum_range_add_sum_Ico _ (show 1 ≤ 32 by simp), Finset.sum_range_one, zero_add]
  rw [Finset.sum_range_id]