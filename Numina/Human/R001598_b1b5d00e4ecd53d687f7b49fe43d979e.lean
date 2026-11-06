import Mathlib

theorem eq_zero_or_hom_of_map_add_map_sq {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [CharZero S] {f : R → S}
    (h : ∀ x y : R, f (x + y) = f x + f y) (h0 : ∀ x : R, f (x ^ 2) = f x ^ 2) :
    f = 0 ∨ ∃ φ : R →+* S, f = φ := by
  suffices ∀ x y, f (x * y) = f x * f y by
    have h1 : f 1 = 0 ∨ f 1 = 1 := by
      specialize h0 1 
      rwa [one_pow, sq, ← sub_eq_zero, ← one_sub_mul,
        mul_eq_zero, sub_eq_zero, eq_comm, or_comm] at h0
    revert h1; refine Or.imp (fun h1 ↦ ?_) (fun h1 ↦ ⟨RingHom.mk' ⟨⟨f, h1⟩, this⟩ h, rfl⟩)
    ext x
    rw [← mul_one x, this, h1, mul_zero]
    simp
  intro x y
  have h1 := h0 (x + y)
  rw [h] at h1
  ring_nf at h1
  rw [h, h, h0, h0] at h1
  repeat rw [add_left_inj] at h1
  rwa [mul_two, h, ← mul_two, mul_left_inj' (by simp)] at h1

theorem f_zero_eq_zero_or_neg_one [CommRing R] [LinearOrderedRing S] {f : R → S}
    (hf : ∀ x y, (f (x + y)) ^ 2 = 2 * f x * f y + max (f (x ^ 2) + f (y ^ 2)) (f (x ^ 2 + y ^ 2))) :
    f 0 = 0 ∨ f 0 = -1 := by
  specialize hf 0 0
  rw [zero_pow (Nat.succ_ne_zero 1), add_zero, mul_assoc, ← sq, two_mul,
    add_assoc, self_eq_add_right, ← neg_eq_iff_add_eq_zero] at hf
  have h : f 0 ≤ 0 := le_of_max_le_right (hf.symm.trans_le <| neg_nonpos.mpr (sq_nonneg _))
  rw [max_eq_right (add_le_of_nonpos_left h), neg_eq_iff_add_eq_zero] at hf
  rw [show f 0 ^ 2 + f 0 = f 0 * (f 0 + 1) by noncomm_ring] at hf
  rw [mul_eq_zero] at hf
  rw [add_eq_zero_iff_neg_eq'] at hf
  conv_rhs at hf => rw [eq_comm]
  exact hf 

theorem main_ineq {R S : Type*} [CommRing R] [LinearOrderedSemiring S] {f : R → S}
    (hf : ∀ x y, (f (x + y)) ^ 2 = 2 * f x * f y + max (f (x ^ 2) + f (y ^ 2)) (f (x ^ 2 + y ^ 2))) (x y : R) :
    2 * f x * f y + (f (x ^ 2) + f (y ^ 2)) ≤ f (x + y) ^ 2 :=
  (add_le_add_left (le_max_left _ _) _).trans_eq (hf x y).symm

lemma solve_real {f : ℝ → ℝ} (h : ∀ x y , f (x + y) = f x + f y) (h0 : ∀ x , f (x ^ 2) = f x ^ 2) :
    f = 0 ∨ f = id := by
  obtain rfl | ⟨φ, rfl⟩  := eq_zero_or_hom_of_map_add_map_sq h h0
  · simp
  · right ; rw [(Real.RingHom.unique).uniq φ]
    rfl
    
theorem case_f_zero_neg_one {f : ℝ → ℝ}
    (hf : ∀ x y, (f (x + y)) ^ 2 = 2 * f x * f y + max (f (x ^ 2) + f (y ^ 2)) (f (x ^ 2 + y ^ 2))) (h : f 0 = -1) :
    f = -1 ∨ f = id - 1  := by
  have h0 (x) : f (x ^ 2) = f x ^ 2 + 2 * f x := by
    specialize hf x 0
    rw [add_zero, zero_pow (by simp), h, mul_neg_one, eq_neg_add_iff_add_eq,
      add_zero, add_comm, max_eq_right (by norm_num)] at hf
    exact hf.symm
  have h1 {t} (ht : f (-t) = f t) : f t < 1 := by
    have h1 := main_ineq hf t (-t)
    rw [neg_sq, h0, ht, add_neg_cancel, h] at h1
    rw [show 2 * f t * f t + (f t ^ 2 + 2 * f t + (f t ^ 2 + 2 * f t)) = (2 * f t) ^ 2 + 2 ^ 2 * f t by ring] at h1
    replace h := le_of_add_le_of_nonneg_right h1 (sq_nonneg _)
    linarith
  rcases em' (∀ t, f (-t) = f t) with h2 | h2
  -- Case 1: `f` is not even
  · suffices h1 : ∀ x y, f (x + y) + 1 = (f x + 1) + (f y + 1) by
      rw [eq_neg_iff_add_eq_zero]; simp only [eq_sub_iff_add_eq]
      refine solve_real h1 fun x ↦ ?_
      change f (x ^ 2) + 1 = (f x + 1) ^ 2
      rw [h0, add_sq, mul_one, one_pow]
    replace h (x y) : f (x + y) - f (-(x + y)) = f (-x) * f (-y) - f x * f y := by
      have h3 := h0 (-(x + y))
      rw [neg_sq, neg_add, h0, add_comm, ← sub_eq_sub_iff_add_eq_add, ← mul_sub, hf, hf,
        neg_sq, neg_sq, add_sub_add_right_eq_sub, mul_assoc, mul_assoc, ← mul_sub,
        ← neg_add, ← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h3
      exact h3.resolve_left two_ne_zero
    replace h0 (x) : f x + f (-x) = -2 := by
      have h3 := h0 (-x)
      rw [neg_sq, h0, add_comm, ← sub_eq_sub_iff_add_eq_add, ← mul_sub,
        sq_sub_sq, ← neg_sub, mul_neg, ← neg_mul, ← sub_eq_zero,
        ← sub_mul, mul_eq_zero, add_comm, sub_eq_zero, sub_eq_zero] at h3
      rcases h3 with h3 | h3; exact h3.symm
      rw [not_forall] at h2; rcases h2 with ⟨t, h2⟩
      replace h0 : f t - f (-t) = f x * (f (-(x + t)) - f (x + t)) := by
        have h4 := h (-x) (x + t); rwa [neg_add_cancel_left, neg_neg, h3, ← mul_sub] at h4
      replace h : f (x + t) - f (-(x + t)) = f x * (f (-t) - f t) := by rw [h, h3, mul_sub]
      rw [← neg_sub (f (x + t)), h, ← mul_neg, neg_sub, ← mul_assoc, ← sq, ← sub_eq_zero,
        ← one_sub_mul, mul_eq_zero, or_iff_left (sub_ne_zero_of_ne (Ne.symm h2)),
        sub_eq_zero, eq_comm, sq_eq_one_iff, or_iff_right (h1 h3).ne] at h0
      rw [h3, h0, ← two_mul, mul_neg_one]
    replace h0 (x) : f (-x) = -(f x + 2) := by rw [neg_add, ← h0 x, neg_add_cancel_left]
    intro x y; specialize h x y
    rw [h0, sub_neg_eq_add, h0, h0] at h
    linarith only [h]
  -- Case 2: `f` is even
  · left 
    replace h1 (t) : f t < 1 := h1 (h2 t)
    replace h (x) : f (x + x) = -1 := by
      have h3 := hf x (-x)
      rw [add_neg_cancel, h, neg_one_sq, neg_sq, h2, ← hf, eq_comm, sq_eq_one_iff] at h3
      exact h3.resolve_left (h1 _).ne
    replace h2 (x) : f x = -1 ∨ (0 < f x ∧ 2 * 2 * (f x ^ 2 + f x) = 1) := by
      specialize hf x x
      rw [h, h, neg_one_sq, ← two_mul, h0, mul_assoc, ← sq] at hf
      refine (le_total (2 * (f x ^ 2 + 2 * f x)) (-1)).imp (fun h3 ↦ ?_) (fun h3 ↦ ?_)
      · rw [max_eq_right h3, eq_add_neg_iff_add_eq, ← two_mul, ← sub_eq_zero, ← mul_sub,
          mul_eq_zero, or_iff_right two_ne_zero, sub_eq_zero, eq_comm, sq_eq_one_iff] at hf
        exact hf.resolve_left (h1 _).ne
      · have h4 : -1 ≤ f x := by
          rw [← neg_neg (f x), neg_le_neg_iff]
          refine le_of_not_lt fun h4 ↦ hf.not_lt
            ((add_le_add_left (le_max_right _ _) _).trans_lt' ?_)
          rw [lt_add_neg_iff_add_lt, ← two_mul, ← neg_sq, mul_lt_mul_left (by norm_num), sq]
          exact one_lt_mul h4.le h4
        rw [max_eq_left h3] at hf  
        rw [show 2 * f x ^ 2 + 2 * (f x ^ 2 + 2 * f x) = 2 * 2 * (f x ^ 2 + f x) by ring] at hf
        refine ⟨lt_of_not_le fun h5 ↦ hf.not_gt (zero_lt_one.trans_le' ?_), hf.symm⟩
        nlinarith
    ext x
    refine (h2 (x ^ 2)).elim (fun h3 ↦ ?_) (fun h3 ↦ (h2 x).resolve_right fun h4 ↦ ?_)
    · rw [h0, eq_neg_iff_add_eq_zero] at h3
      rw [show f x ^ 2 + 2 * f x + 1 = (f x + 1) ^ 2 by ring] at h3
      simp only [Pi.neg_apply, Pi.one_apply]
      nlinarith [h3]
    · suffices f x ^ 2 + f x < f (x ^ 2) ^ 2 + f (x ^ 2) by linarith
      have h5 : f x < f (x ^ 2) := by
        rw [h0] ; linarith
      nlinarith 

/-Denote by $\mathbb{R}$ the set of all real numbers. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that $f(0) \neq 0$ and  $$ f(x+y)^{2}=2 f(x) f(y)+\max \left\{f\left(x^{2}\right)+f\left(y^{2}\right), f\left(x^{2}+y^{2}\right)\right\} $$ for all real numbers $x$ and $y$.-/
theorem Algebra_a7 (f : ℝ → ℝ) (h0 : f 0 ≠ 0)
    (h : ∀ x y, (f (x + y)) ^ 2 = 2 * f x * f y + max (f (x ^ 2) + f (y ^ 2)) (f (x ^ 2 + y ^ 2))) :
    f = -1 ∨ f = id - 1 := by
  obtain h1 | h1 := f_zero_eq_zero_or_neg_one h
  · exact absurd h1 h0
  · exact case_f_zero_neg_one h h1
