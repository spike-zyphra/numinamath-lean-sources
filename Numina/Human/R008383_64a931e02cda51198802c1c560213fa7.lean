import Mathlib

open Polynomial

/- There are exactly $N$ distinct rational numbers $k$ such that $|k|<200$ and
$$
5x^2+kx+12=0
$$
 has at least one integer solution for $x$.  What is $N$?
$\textbf{(A) }6\qquad \textbf{(B) }12\qquad \textbf{(C) }24\qquad \textbf{(D) }48\qquad \textbf{(E) }78\qquad$ -/
theorem algebra_96117 :
    {k : ℚ | |k| < 200 ∧ ∃ x : ℤ, (5 * X ^ 2 + C k * X + 12).eval (x : ℚ) = 0}.ncard = 78 := by
  -- Firstly, 5x^2 + kx + 12 = 0 if and only if k = -5x - 12/x, by definition
  have h_equiv (k : ℚ) (x : ℤ) (hx : x ≠ 0) :
      (5 * X ^ 2 + C k * X + 12).eval (x : ℚ) = 0 ↔ k = -5 * x - 12 / x := by
    constructor <;> intro h
    · simp at h
      have : k * (x : ℚ) = -5 * x ^ 2 - 12 := by linarith
      apply_fun fun a ↦ a * (x : ℚ)⁻¹ at this
      rw [mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hx), mul_one] at this
      rw [this, sub_mul, mul_assoc, sq, mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hx), mul_one,
        inv_eq_one_div, mul_one_div]
    · subst h
      simp
      ring_nf
      rw [mul_inv_cancel₀ (by exact_mod_cast hx), one_mul, sub_self]

  -- Firstly, we prove an auxiliary lemma: |-5x - 12/x| < 400 implies |x| < 40
  -- This follows directly from |-5x - 12/x| = |5x + 12/x| ≥ |5x| for all x
  have aux (x : ℚ) (h : |-5 * x - 12 / x| < 200) : |x| < 40 := by
    rw [sub_eq_add_neg, neg_mul, ← neg_add, abs_neg] at h
    have : |5 * x| ≤ |5 * x + 12 / x| := by
      by_cases hx : 0 ≤ x
      · have : 0 ≤ 5 * x := mul_nonneg (by decide) hx
        have : 0 ≤ 12 / x := div_nonneg (by decide) hx
        rw [abs_eq_self.mpr ‹_›, abs_eq_self.mpr]
        · exact (le_add_iff_nonneg_right ..).mpr this
        · exact add_nonneg ‹_› ‹_›
      · have hx : x ≤ 0 := (not_le.mp hx).le
        have : 5 * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by decide) hx
        have : 12 / x ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by decide) hx
        rw [abs_eq_neg_self.mpr ‹_›, abs_eq_neg_self.mpr]
        · simp [this]
        · exact add_nonpos ‹_› ‹_›
    have := lt_of_le_of_lt this h
    rw [abs_mul, show |(5 : ℚ)| = 5 by rfl] at this
    linarith

  -- Combining the two lemmas, the set of rational numbers k such that |k| < 200 and exists an
  -- integer 5x^2 + kx + 12 = 0 contains precisely numbers of the form -5x - 12/x, with |x| ≤ 39
  -- (excluding x = 0)
  have h :
      {k : ℚ | |k| < 200 ∧ ∃ x : ℤ, x ≠ 0 ∧ k = -5 * x - 12 / x}
        = (fun x : ℤ ↦ -5 * x - 12 / (x : ℚ)) '' {x ∈ Set.Icc (-39) 39 | x ≠ 0} := by
    ext k
    simp only [Set.mem_image, Set.mem_setOf, Set.mem_Icc]
    constructor
    · rintro ⟨hk_abs, x, hx_ne_zero, rfl⟩
      use x, ⟨?_, by exact_mod_cast hx_ne_zero⟩
      have := aux x hk_abs
      rw [abs_lt] at this
      norm_cast at this ⊢
      exact ⟨this.left, by omega⟩
    · rintro ⟨x, ⟨hx, hx_ne_zero⟩, rfl⟩
      use ?_, x, hx_ne_zero
      obtain ⟨hx₁, hx₂⟩ := hx
      interval_cases x <;> native_decide

  have h' : {x : ℤ | x ∈ Set.Icc (-39) 39 ∧ x ≠ 0} = Set.Icc (-39) 39 \ {0} := by
    ext w
    simp

  -- We also show that [-39, 39] - {0} has 78 numbers
  have h'' : {k : ℚ | |k| < 200 ∧ ∃ x : ℤ, x ≠ 0 ∧ k = -5 * x - 12 / x}.ncard = 78 := by
    rw [h, Set.ncard_image_of_injOn]
    · rw [h', Set.ncard_diff]
      · simp [Set.ncard, Set.encard, Int.card_Icc]
      · simp
    · intro x ⟨⟨hx₁, hx₂⟩, hx_ne_zero⟩ y ⟨⟨hy₁, hy₂⟩, hy_ne_zero⟩ h
      simp only at h
      field_simp at h
      have foo : ((5 : ℚ) * x * y - 12) * (x - y) = 0 := by linarith
      qify
      rw [← sub_eq_zero]
      by_contra! h
      simp_all
      norm_cast at foo
      have bar : 5 * (x * y) = 12 := by linarith
      have bar : (5 : ℤ) ∣ 12 := Dvd.intro (x * y) bar
      omega

  -- Finally, we combine all information above to conclude that there are 78 numbers
  convert h'' with k x
  constructor <;> intro hx
  · have : x ≠ 0 := by rintro rfl; simp at hx
    constructor
    · exact_mod_cast this
    · exact (h_equiv k x this).mp hx
  · exact (h_equiv k x hx.left).mpr hx.right