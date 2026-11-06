import Mathlib

open Nat Int

/-
Let  $m_1< m_2 < \ldots m_{k-1}< m_k$  be  $k$  distinct positive integers such that their reciprocals are in arithmetic progression.

1. Show that  $k< m_1 + 2$ .
-/
theorem number_theory_8939_1
    {k : ℕ} [NeZero k]
    (m : ℕ → ℤ)
    (h₀ : ∀ i, 0 < m i)
    (h₁ : ∀ i j, i < j → m i < m j)
    (h₂ : ∃ d, ∀ i, (m i : ℝ)⁻¹ = (m 0 : ℝ)⁻¹ - d * i) :
    k < (m 0) + 2 := by

  rcases eq_or_ne k 1 with hk | hk'
  -- if k = 1, then it can be simply verified
  . simp only [hk, Nat.cast_one]
    linarith [h₀ 0]

  -- otherwise, k > 1
  have hk : k > 1 := one_lt_iff_ne_zero_and_ne_one.mpr ⟨Ne.symm (NeZero.ne' k), hk'⟩

  obtain ⟨d, h₂⟩ := h₂

  -- $d \ge \frac{1}{m_0 (m_0 + 1)}$
  have ⟨rdpos, r1⟩ : d > 0 ∧ (m 0 * (m 0 + 1) : ℝ)⁻¹ ≤ d := by
    specialize h₀ 0
    specialize h₁ 0 1 Nat.one_pos
    specialize h₂ 1
    simp only [one_div, Fin.val_one', one_mod_eq_one.mpr hk', Nat.cast_one, mul_one] at h₂
    have : (m 0 : ℝ)⁻¹ > (m 1 : ℝ)⁻¹ := by
      refine (inv_lt_inv ?_ ?_).mpr ?_
      . norm_cast
        linarith
      . simp only [Int.cast_pos, h₀]
      . simp only [Int.cast_lt, h₁]
    constructor
    . linarith
    . apply ge_iff_le.mp
      calc d
        _ = (m 0 : ℝ)⁻¹ - (m 1 : ℝ)⁻¹ := by linarith
        _ ≥ (m 0 : ℝ)⁻¹ - (m 0 + 1 : ℝ)⁻¹ := by
          have : m 0 + 1 ≤ m 1 := by linarith
          rify at this
          have : (m 1 : ℝ)⁻¹ ≤ (m 0 + 1 : ℝ)⁻¹ := by
            apply inv_le_inv_of_le _ this
            rify at h₀
            linarith
          linarith
        _ = (1 : ℝ) / (m 0 * (m 0 + 1)) := by field_simp
      simp only [one_div, mul_inv_rev, ge_iff_le, le_refl]

  -- since m_{k - 1} > 0, and $m_{k - 1} = \frac{1}{m_0} - d (k - 1) $, we have $\frac{1}{m_0} - d (k - 1) > 0$
  specialize h₂ (k - 1)
  have : (m (k - 1) : ℝ)⁻¹ > 0 := by
    specialize h₀ (k - 1)
    rify at h₀
    exact inv_pos_of_pos h₀
  rw [h₂, Nat.cast_sub (one_le_of_lt hk), Nat.cast_one] at this

  -- then we can get $k < m_0 + 2$.
  have t1 : (m 0 * d)⁻¹ ≤ m 0 + 1 := by
    rw [show m 0 + 1 = (m 0 + 1:ℝ)⁻¹⁻¹ by rw [inv_inv]]
    apply inv_le_inv_of_le
    . apply inv_pos_of_pos
      norm_cast
      linarith [h₀ 0]
    . calc m 0 * d
        _ ≥ m 0 * (m 0 * (m 0 + 1) : ℝ)⁻¹ := by
          apply (mul_le_mul_iff_of_pos_left ?_).mpr r1
          simp only [Int.cast_pos, h₀ 0]
        _ = (m 0 + 1 : ℝ)⁻¹ := by
          simp only [mul_inv_rev]
          rw [← mul_assoc, mul_comm, inv_mul_cancel_left₀]
          simp only [ne_eq, Int.cast_eq_zero]
          linarith [h₀ 0]

  have : d * (k - 1 : ℝ) < (m 0 : ℝ)⁻¹ := by linarith
  apply (lt_div_iff' rdpos).mpr at this
  apply lt_add_of_tsub_lt_right at this
  rw [div_eq_mul_inv, ← mul_inv] at this
  rify
  linarith


/-
Let  $m_1< m_2 < \ldots m_{k-1}< m_k$  be  $k$  distinct positive integers such that their reciprocals are in arithmetic progression.

2. Give an example of such a sequence of length  $k$  for any positive integer  $k$ .
-/
theorem number_theory_8939_2
    {k : ℕ} [NeZero k]
    (hk : k > 0)
    (m : Fin k → ℤ)
    (hm : ∀ x, m x = k ! / (k - x)) :
    (∀ i, 0 < m i) ∧
    (∀ i j, i < j → m i < m j) ∧
    (∃ d, ∀ i, (1 : ℝ) / m i = (1 : ℝ) / (m 0) + d * i) := by

  -- auxiliary lemma for cast div
  have r0 : ∀ i, i < k → (k : ℤ) - i ∣ k ! := by
    intro i hi
    have : k - i ∣ k ! := by
      apply dvd_factorial
      . exact zero_lt_sub_of_lt hi
      . exact sub_le k i
    zify at this
    rw [Nat.cast_sub (by linarith)] at this
    exact this

  have prop1 : ∀ i, 0 < m i := by
    intro ⟨i, hi⟩
    simp only [hm]
    have t1 : k ! > 0 := factorial_pos k
    have t2 : k - i > 0 := zero_lt_sub_of_lt hi
    zify at t1 t2
    rw [Nat.cast_sub (by linarith)] at t2
    apply ediv_pos_of_pos_of_dvd t1 ?_ ?_
    . linarith
    . exact r0 i hi

  have prop2 : ∀ i j, i < j → m i < m j := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [Fin.mk_lt_mk] at hij
    simp only [hm]
    rify
    simp [Int.cast_div, Int.cast_div, Int.cast_add, Int.cast_add]
    have : k ! / (k - i) * (k - j) < k ! := by
      have ⟨x, hx⟩ := dvd_factorial (zero_lt_sub_of_lt hi) (sub_le k i)
      have hxv := (Nat.div_eq_of_eq_mul_right (zero_lt_sub_of_lt hi) hx).symm
      rw [← hxv, hx, mul_comm]
      apply Nat.mul_lt_mul_of_pos_right
      . exact Nat.sub_lt_sub_left hi hij
      . show x > 0
        rw [hxv]
        apply Nat.div_pos ?_ ?_
        . exact Nat.le_trans (sub_le k i) (self_le_factorial k)
        . exact zero_lt_sub_of_lt hi
    zify at this
    rw [Nat.cast_sub (by linarith), Nat.cast_sub (by linarith)] at this
    apply Int.lt_ediv_of_mul_lt (by linarith) ?H2 this
    exact r0 j hj

  have prop3 : ∃ d, ∀ i, (1 : ℝ) / m i = (1 : ℝ) / (m 0) + d * i := by
    use - (k ! : ℝ)⁻¹
    intro ⟨i, hi⟩
    simp [hm]
    rw [Int.cast_div, Int.cast_div, inv_div, inv_div, Int.cast_sub,
        div_eq_inv_mul, div_eq_inv_mul, ← sub_eq_add_neg]
    norm_cast
    simp [← mul_sub]
    any_goals norm_cast
    . refine dvd_factorial hk (Nat.le_refl k)
    . exact not_eq_zero_of_lt hk
    . rw [Int.subNatNat_eq_coe]
      exact r0 i hi
    . have : k - i ≠ 0 := by exact Nat.sub_ne_zero_iff_lt.mpr hi
      zify at this
      rw [Nat.cast_sub (by linarith)] at this
      rw [Int.subNatNat_eq_coe]
      exact this

  exact ⟨prop1, prop2, prop3⟩
