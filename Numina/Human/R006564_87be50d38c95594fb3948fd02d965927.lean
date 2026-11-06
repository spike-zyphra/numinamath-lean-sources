import Mathlib.Data.ZMod.Basic

theorem inv_mod_sub_int {m k : ℕ}
  (hm   : 1 < m)
  (hk1  : 1 ≤ k)
  (hklt : k < m)
  (hg   : Nat.gcd k m = 1) :
  { n : ℕ | n < m ∧ (m - k) * n ≡ 1 [MOD m] } =
    { (m - (k : ZMod m)⁻¹).val } := by

  -- Let `m` be an integer with `1 < m` and `k` an integer with `1 ≤ k < m` and `gcd k m = 1`.
  -- Then the unique solution `n` with `0 ≤ n < m` to `(m - k) * n ≡ 1 [MOD m]` is `n = m - (k : ZMod m)⁻¹`.

  have inv_mod_sub
    : ∀ {m k : ℕ} , (hm : 1 < m) → (hk : k < m) → (h : Nat.gcd k m = 1) →
      ((m - k : ZMod m) * (m - (k : ZMod m)⁻¹) : ZMod m) = 1 := by
    intro m k hm hk h
    -- cast `m` to `0` in `ZMod m`
    have hm0 : (m : ZMod m) = 0 := by exact ZMod.natCast_self m

    -- `k : ZMod m` is non-zero since `gcd k m = 1`
    have hk0 : (k : ZMod m) ≠ 0 := by
      intro h0
      have : m ∣ k := (ZMod.natCast_zmod_eq_zero_iff_dvd k m).mp h0
      have hk_zero : k = 0 := Nat.eq_zero_of_dvd_of_lt this hk
      rw [hk_zero, Nat.gcd_zero_left] at h
      omega

    -- now the calculation
    calc (m - k) * (m - (k : ZMod m)⁻¹)
        = (-k) * (m - (k : ZMod m)⁻¹) := by simp [ZMod.cast_sub]
      _   = (-k) * (- (k : ZMod m)⁻¹) := by simp [ZMod.cast_sub, hm0]
      _   = k * (k : ZMod m)⁻¹          := by simp
      _   = 1                          := by exact ZMod.coe_mul_inv_eq_one k h


  -- first, show the right-hand side actually satisfies the congruence
  let a: ZMod m := m - k
  let b: ZMod m := m - (k : ZMod m)⁻¹.val

  haveI : NeZero m := NeZero.of_pos (zero_lt_one.trans hm)
  have h₀: (k : ZMod m)⁻¹ = ↑((k : ZMod m)⁻¹.val) := (ZMod.natCast_zmod_val ((k : ZMod m)⁻¹)).symm


  have h₁ : a * b = 1 := by
    simp only [a, b]
    rw [← h₀]
    exact inv_mod_sub hm hklt hg

  have h_m_k : ((m: ZMod m) - ↑k) = ↑(m - k):= Eq.symm (Nat.cast_sub (by omega))


  have h₁' : (m - k) * (m - (k : ZMod m)⁻¹).val ≡ 1 [MOD m] := by
    -- according to ZMod.eq_iff_modEq_nat, it suffices to show that
    -- ((m - k) * (m - (k : ZMod m)⁻¹).val): ZMod m = 1 : ZMod m
    let lfs := ((m - k) * (m - (k : ZMod m)⁻¹).val)
    have : (lfs : ZMod m) = ↑(1 : ℕ) := by calc
      _ = ((m - k) * (m - (k : ZMod m)⁻¹).val:  ZMod m) := by
        simp only [lfs]
        push_cast
        rw [h_m_k]
      _ = (m - k : ZMod m) * ((m - (k : ZMod m)⁻¹).val : ZMod m) := by simp only [a, b]
      _ = a * b := by
        have h_a: (m - k : ZMod m) = a := by simp only [a]
        have h_b: (m - (k : ZMod m)⁻¹).val = b := by
          simp only [b]
          rw [← h₀]
          simp only [ZMod.natCast_zmod_val]
        simp only [h_a, h_b]
      _ = 1 := h₁
      _ = ↑(1 : ℕ) :=by exact Eq.symm Nat.cast_one

    exact (ZMod.eq_iff_modEq_nat m).mp this



  -- next, show uniqueness: there is at most one `n < m` satisfying the congruence
  have h₂ : ∀ n n', n < m → n' < m →
    (m - k) * n ≡ 1 [MOD m] → (m - k) * n' ≡ 1 [MOD m] → n = n' := by
    intros n n' hnm hnm' he he'
    -- subtract the two congruences to get `(m-k)*(n - n') ≡ 0`

    have h_inv_1: (m - k: ZMod m)⁻¹ = (n: ZMod m) := by
      have mod_eq := (ZMod.eq_iff_modEq_nat m).mpr he
      have mod_eq': (m - k: ZMod m) * (n: ZMod m)  = 1 := by
        calc
          _ = ((m - k) * n: ZMod m) := by simp only [a, b]
          _ = ↑(1 : ℕ) := by
            rw [← mod_eq]
            rw [h_m_k]
            norm_cast
          _ = 1 :=by exact Nat.cast_one

      exact (ZMod.inv_eq_of_mul_eq_one m (m - k: ZMod m) (n: ZMod m) mod_eq')

    have h_inv_2: (m - k: ZMod m)⁻¹ = (n': ZMod m) := by
      have mod_eq := (ZMod.eq_iff_modEq_nat m).mpr he'
      have mod_eq': (m - k: ZMod m) * (n': ZMod m) = 1 := by
        calc
          _ = ((m - k) * n': ZMod m) := by simp only [a, b]
          _ = ↑(1 : ℕ) := by
            rw [← mod_eq]
            rw [h_m_k]
            norm_cast
          _ = 1 :=by exact Nat.cast_one
      exact (ZMod.inv_eq_of_mul_eq_one m (m - k: ZMod m) (n': ZMod m) mod_eq')

    have h_inv_eq: (n: ZMod m) = (n': ZMod m) := by
      calc
        _ = (m - k: ZMod m)⁻¹ := h_inv_1.symm
        _ = (n': ZMod m) := h_inv_2

    calc
      n = (n: ZMod m).val := by simp only [ZMod.val_natCast_of_lt hnm]
      _ = (n': ZMod m).val := by congr
      _ = n' := by simp only [ZMod.val_natCast_of_lt hnm']

  -- now assemble the set equality
  ext n
  simp only [Set.mem_singleton_iff, Set.mem_setOf, Subtype.coe_mk]
  constructor
  · intro ⟨hnm, heq⟩
    -- existence + uniqueness forces `n = ...`
    exact h₂ n ((m - (k : ZMod m)⁻¹).val) hnm (ZMod.val_lt _) heq h₁'
  · intro hn_eq
    -- the witness `(m - (k : ZMod m)⁻¹).val` obviously satisfies both
    rw [hn_eq]
    constructor
    · exact ZMod.val_lt _
    · exact h₁'