import Mathlib
open Classical

/- Let $a$ and $b$ be two positive integers. Prove that the integer  $$ a^{2}+\left\lceil\frac{4 a^{2}}{b}\right\rceil $$  is not a square. (Here $\lceil z\rceil$ denotes the least integer greater than or equal to $z$.) -/
theorem number_theory_23816
    (a b : ℕ)
    (ha : 0 < a)
    (hb : 0 < b) :
    ¬ ∃ x, x ^ 2 = a ^ 2 + ⌈(4 * a ^ 2 / b : ℝ)⌉ := by
  -- assume that a ^ 2 + ⌈(4 * a ^ 2 / b : ℝ)⌉ = (a + k) ^ 2
  by_contra h
  obtain ⟨n, hn⟩ := h
  have hn : a ^ 2 + ⌈(4 * a ^ 2 / b : ℝ)⌉ = n.natAbs ^ 2 := by
    rw [←hn]
    exact Int.natAbs_eq_iff_sq_eq.mp rfl
  have hngea : n.natAbs ≥ a := by
    have : (n.natAbs ^ 2 : ℤ) ≥ a ^ 2 := by
      rw [←hn]
      apply Int.le_add_of_nonneg_right
      apply Int.ceil_nonneg
      apply div_nonneg
      · apply mul_nonneg
        · exact zero_le_four
        · apply pow_two_nonneg
      · exact Nat.cast_nonneg' b
    apply sq_le_sq.mp at this
    simp at this
    rw [←Int.natCast_natAbs] at this
    exact Int.ofNat_le.mp this
  let k := n.natAbs - a
  have hneq : n.natAbs = a + k := by simp [k]; exact Eq.symm (Nat.add_sub_of_le hngea)
  simp [hneq] at hn
  -- or ⌈(2 * a) ^ 2 / (b : ℝ)⌉ = (2 * a + k) * k
  have hkeq : ⌈(2 * a) ^ 2 / (b : ℝ)⌉ = (2 * a + k) * k := by
    calc
      ⌈(2 * a) ^ 2 / (b : ℝ)⌉ = ⌈4 * a ^ 2 / (b : ℝ)⌉ := by ring_nf
      _ = (a + k) ^ 2 - a ^ 2 := by rw [←hn]; ring
      _ = (2 * a + k) * k := by rw [add_sq, add_mul, pow_two, pow_two]; ring

  -- the equation ⌈c ^ 2 / (b : ℝ)⌉ = (c + k) * k has a nonnegative solution
  let p : ℕ → Prop := fun k => ∃ c : ℕ, c > 0 ∧ ⌈c ^ 2 / (b : ℝ)⌉ = (c + k) * k
  have one_sol : ∃ k, p k := by
    use k, 2 * a
    simp [hkeq, ha]

  -- the equation ⌈c ^ 2 / (b : ℝ)⌉ = (c + k) * k has a minimal nonnegative solution
  let k := Nat.find one_sol
  have hmin : p k := by
    apply Nat.find_spec one_sol
  have hmin' : ∀ k', k' < k → ¬ p k' := by
    intro k'
    exact Nat.find_min one_sol
  obtain ⟨c, ⟨hcpos, hceq⟩⟩ := hmin

  -- clearly, k ≥ 1
  have hkpos : k > 0 := by
    by_contra hkpos
    simp at hkpos
    simp [hkpos] at hceq
    have : ¬ c ^ 2 / b ≤ (0 : ℝ) := by
      simp
      apply div_pos
      · apply pow_pos; exact Nat.cast_pos'.mpr hcpos
      · exact Nat.cast_pos'.mpr hb
    simp [this] at hceq

  -- it can be seen that c > b * k > c - k
  have hcgtbk : c > k * b := by
    have : k ^ 2 ≥ (1 : ℝ) := by
      apply one_le_pow₀
      exact Nat.one_le_cast.mpr hkpos
    have : (c ^ 2 / b : ℝ) > c * k := by
      calc
        (c ^ 2 / b : ℝ) = (c ^ 2 / b : ℝ) + 1 - 1 := by simp
        _ > ⌈c ^ 2 / (b : ℝ)⌉ - 1 := by rel [Int.ceil_lt_add_one (c ^ 2 / (b : ℝ))]
        _ = c * k + k ^ 2 - 1 := by simp [hceq]; ring
        _ ≥ c * k + 1 - 1 := by rel [this]
        _ = c * k := by simp
    have : c * k * b < (c ^ 2 : ℝ) := by
      apply (lt_div_iff₀ ?_).mp
      · exact this
      · exact Nat.cast_pos'.mpr hb
    norm_cast at this
    rw [pow_two, mul_assoc] at this
    exact (Nat.mul_lt_mul_left hcpos).mp this

  have hbkgt : k * b > c - (k : ℤ) := by
    have : (c + k) * k > (c - k) * (c + k) / (b : ℝ) := by
      calc
        (c + k) * (k : ℝ) = ⌈c ^ 2 / (b : ℝ)⌉ := by simp [hceq]
        _ ≥ c ^ 2 / (b : ℝ) := by exact Int.le_ceil _
        _ > (c - k) * (c + k) / (b : ℝ) := by
          apply (lt_div_iff₀ ?_).mpr
          · field_simp
            ring_nf
            apply sub_lt_self
            norm_cast
            exact Nat.pos_pow_of_pos 2 hkpos
          · exact Nat.cast_pos'.mpr hb
    have : (c - k) * (c + k) < (c + k) * k * (b : ℝ) := by
      apply (div_lt_iff₀ ?_).mp
      · exact this
      · exact Nat.cast_pos'.mpr hb
    rw [mul_comm, mul_assoc] at this
    norm_cast at this ⊢
    rw [Nat.cast_mul] at this
    exact lt_of_nsmul_lt_nsmul_right (c + k) this

  -- so c = k * b + r with some 0 < r < k
  let r := c - k * b
  have hreq : c = k * b + r := by
    simp [r]
    rw [Nat.add_sub_cancel']
    exact Nat.le_of_succ_le hcgtbk
  have hrpos : r > 0 := by
    simp [r, hcgtbk]
  have hrltk : r < k := by
    simp [r]
    have : c < k * b + (k : ℤ) := by exact Int.sub_lt_iff.mp hbkgt
    apply Nat.sub_lt_left_of_lt_add
    · exact Nat.le_of_succ_le hcgtbk
    · norm_cast at this

  -- By substituting this in (1) we get ⌈(c ^ 2) / (b : ℝ)⌉ = k ^ 2 * b + 2 * k * r + ⌈r ^ 2 / (b : ℝ)⌉
  have hsub1 : ⌈(c ^ 2) / (b : ℝ)⌉ = k ^ 2 * b + 2 * k * r + ⌈r ^ 2 / (b : ℝ)⌉ := by
    calc
      ⌈(c ^ 2) / (b : ℝ)⌉ = ⌈(k * b + r) ^ 2 / (b : ℝ)⌉ := by rw [hreq]; norm_cast
      _ = ⌈(k ^ 2 * b * b + 2 * k * r * b + r ^ 2) / (b : ℝ)⌉ := by congr; ring
      _ = ⌈k ^ 2 * b + 2 * k * r + (r ^ 2) / (b : ℝ)⌉ := by congr; field_simp; ring
      _ = k ^ 2 * b + 2 * k * r + ⌈r ^ 2 / (b : ℝ)⌉ := by
        norm_cast
        rw [add_comm, Int.ceil_add_nat, add_comm]

  -- and (c + k) * k = k ^ 2 * b + 2 * k * r + k * (k - r)
  have hsub2 : (c + k) * k = k ^ 2 * b + 2 * k * r + k * (k - r : ℤ) := by
    simp [hreq]
    ring_nf

  -- so ⌈(r ^ 2) / (b : ℝ)⌉ = (r + k - r) * (k - r)
  have hr : ⌈(r ^ 2) / (b : ℝ)⌉ = (r + (k - r)) * (k - r) := by
    rw [hceq, hsub2] at hsub1
    simp at hsub1
    rw [←hsub1]
    ring

  -- (r,k-r) provides another positive integer solution
  have hnewsol : p (k - r) := by
    use r
    have : (k - r : ℕ) = k - (r : ℤ) := by
      rw [Nat.cast_sub]
      exact Nat.le_of_succ_le hrltk
    constructor
    · exact hrpos
    · simp [hr, this]

  -- but this contradicts the minimality of k
  have : ¬ p (k - r) := by
    apply hmin'
    exact Nat.sub_lt hkpos hrpos

  contradiction
