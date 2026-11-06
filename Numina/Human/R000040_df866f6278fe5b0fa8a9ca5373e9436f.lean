import Mathlib

set_option maxRecDepth 5000

open Cardinal
open Complex hiding abs_of_nonneg

/-- `f z` denotes that $z ^ 2 + i * z + 1$. -/
def f_4086 (z : ℂ) := z ^ 2 + I * z + 1

/-- Auxiliary lemma : one transform of `f z`. -/
lemma f_eq (z : ℂ) : f_4086 z = (z + I / 2) ^ 2 + 5 / 4 := by
  ring_nf; rw [f_4086, Complex.I_sq]; ring

/-- Auxiliary lemma : the quadratic formula. -/
lemma Complex.sqrt_eq {z w : ℂ} : z ^ 2 = w ↔ z = w ^ (1 / 2 : ℂ) ∨ z = -w ^ (1 / 2 : ℂ) := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · have h : z ^ 2 = (w ^ (1 / 2 : ℂ)) ^ 2 := by simpa
    rwa [sq_eq_sq_iff_eq_or_eq_neg] at h
  · cases' h with h h <;> simp [h]

/-- Auxiliary lemma : A Lemma on the Square Roots of Complex Numbers. -/
lemma Complex.abs_sqrt_im {z : ℂ} : |(z ^ (1 / 2 : ℂ)).im| = ((‖z‖ - z.re) / 2).sqrt := by
  simp only [cpow_def, div_eq_zero_iff, one_ne_zero, OfNat.ofNat_ne_zero, or_self, ↓reduceIte]
  split_ifs with h
  · simp [h]
  · rw [show (1 / 2 : ℂ) = (1 / 2 : ℝ) by simp, Complex.exp_im,
      Complex.re_mul_ofReal, Complex.im_mul_ofReal, Complex.log_re, Complex.log_im,
      ← Real.rpow_def_of_pos (by simpa), ← Real.sqrt_eq_rpow, abs_mul,
      mul_one_div, Real.abs_sin_half, _root_.abs_of_nonneg (by apply Real.sqrt_nonneg),
      ← Real.sqrt_mul (by simp)]
    congr 1
    field_simp [mul_sub]

/-- Auxiliary lemma : the image part of complex number $z$ greater than $1/2$ if and only if its square root $w$ satisfy that `1 + 4 * w.re < 4 * w.im ^ 2`. -/
lemma lemma1 : (∃ z : ℂ, z.im > 1 / 2 ∧ z ^ 2 = w) ↔ 1 + 4 * w.re < 4 * w.im ^ 2 := by
  refine Iff.trans (?_ : _ ↔ |(w ^ (1 / 2 : ℂ)).im| > 1 / 2) ?_
  · simp only [Complex.sqrt_eq]
    refine Iff.intro (fun ⟨x, h₁, h₂⟩ => ?_) (fun h => ?_)
    · cases' h₂ with h₂ h₂
      · rwa [← h₂, abs_of_nonneg (by linarith)]
      · rwa [show w ^ (1 / 2 : ℂ) = -x by simp [h₂], Complex.neg_im,
          abs_neg, abs_of_nonneg (by linarith)]
    · by_cases h' : 0 ≤ (w ^ (1 / 2 : ℂ)).im
      · rw [abs_of_nonneg (by assumption)] at h
        use w ^ (1 / 2 : ℂ); simpa using h
      · rw [abs_of_nonpos (by linarith)] at h
        use -w ^ (1 / 2 : ℂ); simpa using h
  · rw [Complex.abs_sqrt_im]
    conv_lhs => change 1 / 2 < √((‖w‖ - w.re) / 2)
    have sqrt_4 : 2 = √4 := by
      (have h := (Real.sqrt_sq_eq_abs 2).symm); norm_num at h; exact h
    rw [show 1 / 2 = √ (1 / 4) by simpa,
      Real.sqrt_lt_sqrt_iff (by simp), ← sub_lt_zero,
      show 1 / 4 - (‖w‖ - w.re) / 2 = (1 + 2 * w.re - 2 * ‖w‖) / 4 by ring,
      show (0 : ℝ) = 0 / 4 by simp, div_lt_div_right (by simp),
      sub_lt_zero, Complex.norm_eq_abs, Complex.abs_eq_sqrt_sq_add_sq]
    nth_rw 2 [sqrt_4]
    rw [← Real.sqrt_mul (by simp)]
    by_cases h : 0 ≤ 1 + 2 * w.re
    · rw [Real.lt_sqrt h, ← sub_lt_zero]
      conv_rhs => rw [← sub_lt_zero]
      ring_nf
    · simp only [not_le] at h
      simp only [
        show 1 + 2 * w.re < √(4 * (w.re ^ 2 + w.im ^ 2)) from
          lt_of_lt_of_le h (Real.sqrt_nonneg _),
        show 1 + 4 * w.re < 4 * w.im ^ 2 from
          lt_of_lt_of_le (b := 0) (by linarith) (by positivity)]

/-- Auxiliary lemma : the imaginary part of the imaginary number $z$ is positive and `f z = w` if and only if `w.im ^ 2 > w.re - 1`. -/
lemma lemma2 : (∃ z : ℂ, z.im > 0 ∧ f_4086 z = w) ↔ w.im ^ 2 > w.re - 1 := by
  simp only [f_eq, ← eq_sub_iff_add_eq]
  transitivity ∃ z, z.im > 1 / 2 ∧ z ^ 2 = w - 5 / 4
  · refine ⟨fun ⟨z, h⟩ => ?_, fun ⟨z, h⟩ => ?_⟩
    · use z + I / 2; simpa using h
    · use z - I / 2; simpa using h
  · rw [lemma1, gt_iff_lt, ← sub_lt_zero, iff_eq_eq]
    conv_rhs => rw [← sub_lt_zero, ← mul_lt_mul_left (show 0 < (4 : ℝ) by simp)]
    congr 1
    · simp [← sub_eq_zero]; ring
    · norm_num

/-- Let $f : \mathbb{C} \to \mathbb{C} $ be defined by $ f(z) = z^2 + iz + 1 $. How many complex numbers $z $ are there such that $ \text{Im}(z) > 0 $ and both the real and the imaginary parts of $f(z)$ are integers with absolute value at most $ 10 $?-/
theorem intermediate_algebra_4086 : #{z : ℂ | z.im > 0 ∧
    (f_4086 z).re ∈ Set.range Int.cast ∧ |(f_4086 z).re| ≤ 10 ∧
    (f_4086 z).im ∈ Set.range Int.cast ∧ |(f_4086 z).im| ≤ 10} = 399 := by
  set X := {z : ℂ | z.im > 0 ∧
    (f_4086 z).re ∈ Set.range Int.cast ∧ |(f_4086 z).re| ≤ 10 ∧
    (f_4086 z).im ∈ Set.range Int.cast ∧ |(f_4086 z).im| ≤ 10}
  -- Here `Y` is a `Finset` with a computed property, that is, `Finset.card Y` is defined to be equal to 399.
  -- In other words, Lean can automatically enumerate the elements in `Y` and calculate the number.
  let Y := (Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10) 10)
    |>.filter (fun ⟨a, b⟩ => b ^ 2 > a - 1)
  transitivity #Y
  · -- just need to prove `X ≃ { x // x ∈ Y }`.
    apply Cardinal.mk_congr
    let a {z} (hz : z ∈ X) : ℤ := hz.2.1.choose
    let b {z} (hz : z ∈ X) : ℤ := hz.2.2.2.1.choose
    have a_eq {z} (hz : z ∈ X) : a hz = (f_4086 z).re := by simp only [hz.2.1.choose_spec]
    have b_eq {z} (hz : z ∈ X) : b hz = (f_4086 z).im := by simp only [hz.2.2.2.1.choose_spec]
    have mem_Y (a b : ℤ) : (a, b) ∈ Y ↔ (|a| <= 10 ∧ |b| <= 10) ∧ b ^ 2 > a - 1 := by
      simp [Y, ← abs_le]
    have qab {z} (hz : z ∈ X) : (a hz, b hz) ∈ Y := by
      rw [mem_Y]
      rify
      rw [a_eq hz, b_eq hz]
      apply And.intro
      · exact ⟨hz.2.2.1, hz.2.2.2.2⟩
      · rw [← gt_iff_lt, ← lemma2]
        exact ⟨z, ⟨hz.1, rfl⟩⟩
    -- constructor the equivlence from the function `(fun ⟨z, hz⟩ => ⟨(a hz, b hz), qab hz⟩)` which from `X` to `{ x // x ∈ Y }` is bijective.
    apply Equiv.ofBijective (fun ⟨z, hz⟩ => ⟨(a hz, b hz), qab hz⟩)
    constructor
    · --the above function is injective.
      intro ⟨z, hz⟩ ⟨z', hz'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      rify at h
      rw [a_eq hz, a_eq hz', b_eq hz, b_eq hz'] at h
      replace h : f_4086 z = f_4086 z' := Complex.ext h.1 h.2
      simp only [f_eq, add_left_inj, sq_eq_sq_iff_eq_or_eq_neg] at h
      congr 1
      cases' h with h h
      · assumption
      · replace hz := hz.1
        replace hz' := hz'.1
        apply_fun Complex.im at h
        have : z.im + z'.im = -1 := by
          rw [← sub_eq_zero] at h ⊢
          exact Eq.trans (by simp; ring) h
        have : (-1 : ℝ) > 0 := this.symm ▸ add_pos hz hz'
        norm_num at this
    · -- the above function is surjective.
      intro ⟨⟨a', b'⟩, h⟩
      rw [mem_Y] at h
      rify at h
      obtain ⟨z, hz⟩ := lemma2 (w := ⟨a', b'⟩) |>.mpr h.2
      have hz' : z ∈ X := by simpa [X, Set.mem_setOf_eq, hz.2] using ⟨hz.1, h.1⟩
      use ⟨z, hz'⟩
      dsimp only [Set.coe_setOf]
      congr 2
      · rify; rw [a_eq hz', hz.2]
      · rify; rw [b_eq hz', hz.2]
  · simp only [Cardinal.mk_coe_finset, Y]
    rfl
