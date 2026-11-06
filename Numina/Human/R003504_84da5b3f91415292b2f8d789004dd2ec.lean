import Mathlib

namespace algebra_189042
/- 20. Given that $a$ is a positive real number, $b$ is a positive integer and $2 \leqslant b \leqslant 200$, then the number of pairs $(a, b)$ that satisfy $\left(\log _{b} a\right)^{2017}=\log _{b} a^{2017}$ is $(\quad)$.
(A) 198
(B) 199
(C) 398
(D) 399
(E) 597 -/

lemma l_encard_prod {α β : Type*} {s : Set α} {t : Set β}: (s ×ˢ t).encard = s.encard * t.encard := by
  unfold Set.encard
  rw [ENat.card_congr (Equiv.Set.prod ..)]
  simp [ENat.card]

lemma l_ncard_prod {α β : Type*} {s : Set α} {t : Set β}: (s ×ˢ t).ncard = s.ncard * t.ncard := by
  unfold Set.ncard ENat.toNat
  rw [l_encard_prod]
  cases s.encard <;> cases t.encard <;> rw [WithTop.untop'_zero_mul]

lemma l_rpow_right_inj {x y z:ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) : x ^ y = x ^ z ↔ y = z := by
  refine ⟨fun H ↦ ?_, fun H ↦ by rw [H]⟩
  rcases hx₁.lt_or_lt with h | h
  · exact (Real.strictAnti_rpow_of_base_lt_one hx₀ h).injective H
  · exact (Real.strictMono_rpow_of_base_gt_one h).injective H

lemma l_rpow_left_inj {x y z :ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z ≠ 0) : x ^ z = y ^ z ↔ x = y := by
  constructor
  case mp =>
    intro hxy
    rw [← Real.rpow_one x, ← Real.rpow_one y, ← mul_inv_cancel₀ hz, Real.rpow_mul hx, Real.rpow_mul hy, hxy]
  case mpr => intro h; rw [h]

lemma lemma_1 (x : ℝ) : x^(2017) = 2017 * x ↔ x = 0 ∨ x = 2017^(1/2016:ℝ) ∨ x = -(2017^(1/2016:ℝ)) := by
  -- The equasion x^2017 = 2017*x has three roots: x=0, x = 2017^(1/2016) and x = -(2017^(1/2016))
  constructor
  case mp =>
    intro h
    by_cases x=0
    case pos => left; trivial
    case neg h_neq =>
      -- If x ≠ 0, then x^2016 = 2017, so x = ± 2017^(1/2016).
      right
      rify at h
      rw [pow_succ] at h
      simp at h
      cases h
      case inl h => 
        wlog h_x_pos : 0 ≤ x
        case inr =>
          simp
          simp at h_x_pos
          specialize this (-x)
          simp at this
          specialize this h_neq ?h2 (by linarith)
          case h2 =>
            rw [neg_pow]
            norm_num
            assumption
          cases this
          case inl h =>
            right
            apply_fun (fun x => -x) at h
            simp at h
            assumption
          case inr h =>
            left
            assumption
        left
        apply_fun (fun x => x^(1/2016:ℝ)) at h
        simp at h
        rw [← Real.rpow_natCast] at h
        have : (2016:ℝ) = ↑(2016:ℕ) := by simp
        rw [this] at h
        rw [Real.rpow_rpow_inv h_x_pos (by simp)] at h
        rw [h]
        simp
      case inr h => contradiction
  case mpr =>
    intro h
    casesm* _ ∨ _ <;> subst_eqs
    case inl => simp
    case inr.inl =>
      rw [pow_succ, ← Real.rpow_natCast]
      simp
    case inr.inr =>
      rw [pow_succ]
      simp
      rw [neg_eq_neg_one_mul, mul_pow]
      norm_num
      rw [← Real.rpow_natCast]
      simp

lemma lemma_2 : {(a, b) : ℝ × ℕ | 0 < a ∧ 2 ≤ b ∧ b ≤ 200 ∧ (Real.logb b a) ^ 2017 = Real.logb b (a ^ 2017)}
    = {(a, b) : ℝ × ℕ | 0 < a ∧ 2 ≤ b ∧ b ≤ 200 ∧ (Real.logb b a = 0 ∨ Real.logb b a = 2017^(1/2016:ℝ) ∨ Real.logb b a = -2017^(1/2016:ℝ))} := by
  -- By x= log_b(a), and rewriting log_b(a^2017) = 2017*lob_b(a), we get x^2017 = 2017*x
  -- By lemma_1, this has three roots: x=0, x = 2017^(1/2016) and x = -(2017^(1/2016))
  -- As a result, the set where log_b(a)^2017 = log_b(a^2017) is the same as the set where log_b(a) is one of those three roots
  ext pair
  obtain ⟨a,b⟩ := pair
  simp only [Set.mem_setOf_eq, and_congr_right_iff]
  intro ha hb_low hb_upp
  constructor
  case mp =>
    intro h_eq
    nth_rw 2 [← Real.rpow_natCast] at h_eq
    rw [Real.logb_rpow_eq_mul_logb_of_pos ha] at h_eq
    apply (lemma_1 (Real.logb b a)).mp h_eq
  case mpr =>
    intro h
    nth_rw 2 [← Real.rpow_natCast]
    rw [Real.logb_rpow_eq_mul_logb_of_pos ha]
    apply (lemma_1 (Real.logb b a)).mpr h

noncomputable def f : ℕ × Fin 3 → ℝ × ℕ := fun (b, c) => match c with
 | 0 => (1, b+2)
 | 1 => ((b+2)^(2017^(1/2016:ℝ):ℝ), b+2)
 | 2 => ((b+2)^(-2017^(1/2016:ℝ):ℝ), b+2)

lemma l_f_inj : Set.InjOn f (Finset.range 199 ×ˢ Finset.univ) := by
  -- f is injective, (on the domain), because based on the element form Fin 3,
  -- the first part of the result is either 1, greater than 1 or less than 1.
  rintro ⟨n,i⟩ ⟨hn,_⟩ ⟨m,j⟩ ⟨hm, _⟩ h_eq
  wlog hij : i≤j
  · simp at hij
    symm
    apply this m j _ _ n i _ _
    all_goals try assumption
    case h_eq => symm; assumption
    case hij => omega
  unfold f at h_eq
  simp
  constructor
  case left =>
    fin_cases i <;> fin_cases j <;> simp at h_eq <;> omega
  case right =>
    have : (0:ℝ) < 2017 ^ ((2016:ℝ)⁻¹) := by
      apply Real.rpow_pos_of_pos
      norm_num
    fin_cases i <;> fin_cases j <;> simp at h_eq
    all_goals simp
    all_goals simp at hij
    case «0».«1» =>
      obtain ⟨h_eq, _⟩ := h_eq
      subst_eqs
      have : (1:ℝ) = 1 ^(2017 ^ (2016:ℝ)⁻¹ :ℝ) := by simp
      rw [this] at h_eq
      apply (l_rpow_left_inj (by linarith) (by linarith) (by linarith)).mp at h_eq
      norm_cast at h_eq
      simp at h_eq
    case «0».«2» =>
      obtain ⟨h_eq, _⟩ := h_eq
      subst_eqs
      have : (1:ℝ) = 1 ^(-2017 ^ (2016:ℝ)⁻¹ :ℝ) := by simp
      rw [this] at h_eq
      apply (l_rpow_left_inj (by linarith) (by linarith) (by linarith)).mp at h_eq
      norm_cast at h_eq
      simp at h_eq
    case «1».«2» =>
      obtain ⟨h_eq, _⟩ := h_eq
      subst_eqs
      apply (l_rpow_right_inj (by linarith) (by linarith)).mp at h_eq
      linarith

lemma lemma_4 : {(a, b) : ℝ × ℕ | 0 < a ∧ 2 ≤ b ∧ b ≤ 200 ∧ (Real.logb b a = 0 ∨ Real.logb b a = 2017^(1/2016:ℝ) ∨ Real.logb b a = -2017^(1/2016:ℝ))}
    = f '' Finset.range 199 ×ˢ Finset.univ := by
  -- When f is applied to the range 0-199 × {0,1,2}, it gives exactly the desired set,
  -- since the value of a is chosen such that they give exactly the three possible values of log_b(a)
  ext pair
  obtain ⟨a,b⟩ := pair
  simp only [Nat.cast_eq_zero, Nat.cast_eq_one, one_div, Set.mem_setOf_eq, Finset.coe_range, Finset.coe_univ, Set.mem_image, Set.mem_prod, Set.mem_Iio, Set.mem_univ, and_true, Prod.exists, exists_and_left]
  constructor
  case mp =>
    rintro ⟨ha, hb_low, hb_upp, h⟩
    use b-2
    constructor
    case left => omega
    case right =>
      unfold f
      casesm* _ ∨ _
      case inl h =>
        use 0; simp
        constructor
        case right => omega
        case left =>
          simp at h
          casesm* _∨_ <;> linarith
      case inr.inl h =>
        use 1; simp
        constructor
        case right => omega
        case left =>
          apply_fun (fun x => (b^x :ℝ)) at h
          rw [Real.rpow_logb] at h
          case b_pos => norm_cast; linarith
          case b_ne_one => norm_cast; linarith
          case hx => linarith
          rw [h]
          congr
          norm_cast
          omega
      case inr.inr h =>
        use 2; simp
        constructor
        case right => omega
        case left =>
          apply_fun (fun x => (b^x :ℝ)) at h
          rw [Real.rpow_logb] at h
          case b_pos => norm_cast; linarith
          case b_ne_one => norm_cast; linarith
          case hx => linarith
          rw [h]
          congr
          norm_cast
          omega
  case mpr =>
    rintro ⟨b', hb, i, h⟩
    unfold f at h
    have : b = b'+2 := by fin_cases i <;> simp at h <;> obtain ⟨_,h⟩ := h <;> rw [h]
    constructorm* _ ∧ _
    case right.left => linarith
    case right.right.left => linarith
    case left =>
      fin_cases i
      case «0» => subst_eqs; norm_num
      all_goals simp at h
      all_goals obtain ⟨h,_⟩ := h
      all_goals subst_eqs
      all_goals apply Real.rpow_pos_of_pos
      all_goals norm_cast
      all_goals simp
    case right.right.right =>
      fin_cases i
      case «0» =>
        left
        simp at h
        obtain ⟨h,_⟩ := h
        subst_eqs
        simp
      case «1» =>
        right; left
        simp at h
        obtain ⟨left,right⟩ := h
        subst_vars
        simp
        rw [Real.logb_rpow]
        case b_pos => norm_cast; simp
        case b_ne_one => norm_cast; simp
      case «2» =>
        right; right
        simp at h
        obtain ⟨left,right⟩ := h
        subst_vars
        simp
        rw [Real.logb_rpow]
        case b_pos => norm_cast; simp
        case b_ne_one => norm_cast; simp

end algebra_189042

open algebra_189042
theorem algebra_189042 :
    {(a, b) : ℝ × ℕ | 0 < a ∧ 2 ≤ b ∧ b ≤ 200 ∧ (Real.logb b a) ^ 2017 = Real.logb b (a ^ 2017)}.ncard = 597 := by
  -- This equasion holds if and only if log_b(a) is one of 0, 2017^(1/2016) and -2017^(1/2016)
  rw [lemma_2]
  -- For each value of b, there is one value of a that gives each of these values of log_b(a)
  rw [lemma_4]
  -- Since these values are also distinct, there are 199*3 = 597 distinct pairs
  rw [Set.ncard_image_of_injOn l_f_inj]
  rw [l_ncard_prod]
  rw [Set.ncard_coe_Finset, Finset.card_range]
  rw [Set.ncard_coe_Finset, Finset.card_fin]