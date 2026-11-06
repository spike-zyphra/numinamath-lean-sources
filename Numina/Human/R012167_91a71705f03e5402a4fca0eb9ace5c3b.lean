import Mathlib

open Polynomial Real

/- 1. Let $\operatorname{tg} \alpha$ and $\operatorname{tg} \beta$ be the real roots of the quadratic equation $x^{2}+p x+q=0$. What conditions must $p$ and $q$ satisfy for $\alpha+\beta=60^{\circ}+k \cdot 180^{\circ}$ to hold? -/

-- lemma stating vieta theorems for roots x, y for a monic quadratic
lemma l_vieta_sum {a b x y : ℝ} (h : (X^2 + C a * X + C b).roots = {x, y}) : x + y = -a ∧
    x * y = b := by
  have h_deg : (X^2 + C a * X + C b).natDegree = 2 := by
    compute_degree!
  have h_monic : (X^2 + C a * X + C b).Monic := by
    simp [h_deg, Monic, leadingCoeff]
  have h_splits : Splits (RingHom.id ℝ) (X^2 + C a * X + C b) := by
    rw [splits_iff_card_roots, h_deg, h]
    simp
  and_intros
  . suffices a = - (x + y) by linarith
    convert sum_roots_eq_nextCoeff_of_monic_of_split h_monic h_splits
    . simp [nextCoeff, h_deg]
    . simp [h]
  . suffices b = x * y by linarith
    convert prod_roots_eq_coeff_zero_of_monic_of_splits h_monic h_splits using 1
    . simp
    . simp [h_deg, h]

-- lemma for 0 ≤ (x - a) * (x - b), particularly that x ≤ a ∨ b ≤ x
lemma l_quadratic_nonneg (x a b : ℝ) (h : a ≤ b) : 0 ≤ (x - a) * (x - b) ↔ x ≤ a ∨ b ≤ x := by
   rw [mul_nonneg_iff, sub_nonneg, sub_nonneg, sub_nonpos, sub_nonpos,
     and_iff_right_of_imp h.trans, and_iff_left_of_imp h.trans', or_comm]

-- we can write any x as r + k * π where r ∈ [π/2, π/2), useful for trigonometry
lemma l_exists_in_period (x : ℝ) : ∃ (k : ℤ), ∃ (r : ℝ), x = r + k * π ∧ -π/2 ≤ r ∧ r < π/2 := by
  use ⌊(x + π/2)/π⌋, x - ⌊(x + π/2)/π⌋ * π
  and_intros
  . linarith
  . suffices ⌊(x + π / 2) / π⌋ * π ≤ x + π / 2 by linarith
    rw [← le_div_iff₀ pi_pos]
    exact Int.floor_le ((x + π / 2) / π)
  . suffices x + π / 2 - π < ⌊(x + π / 2) / π⌋ * π by linarith
    rw [← div_lt_iff₀ pi_pos]
    convert_to (x + π / 2) / π - 1 < ⌊(x + π / 2) / π⌋
    . field_simp
    exact Int.sub_one_lt_floor ((x + π / 2) / π)

theorem algebra_225635 {α β p q : ℝ} (hα : ∀ (k : ℤ), α ≠ (2 * k + 1) * π / 2)
    (hβ : ∀ (k : ℤ), β ≠ (2 * k + 1) * π / 2) (h : (X^2 + C p * X + C q).roots = {tan α, tan β}) :
    (∃ (k : ℤ), α + β = π / 3 + k * π) ↔ (q ≤ 1 / 3 ∨ q ≥ 3) ∧ p = (q - 1) * √3 := by
  -- obtain vieta facts
  obtain ⟨hsum, hprod⟩ := l_vieta_sum h
  -- write tan addition formula and plug in the hsum and hprod
  have h_tan_add := tan_add' ⟨hα, hβ⟩
  rw [hsum,hprod] at h_tan_add
  -- tan α is a root of quadratic, so discriminant is a square hence nonnegative, which gives 4q ≤ p^2
  have h_eval : 1 * (tan α * tan α) + p * tan α + q = 0 := by
    convert_to (X^2 + C p * X + C q : ℝ[X]).eval (tan α) = 0
    . simp [sq]
    apply Polynomial.IsRoot.eq_zero
    apply Polynomial.isRoot_of_mem_roots
    rw [h]
    simp
  have h_discrim := discrim_eq_sq_of_quadratic_eq_zero h_eval
  replace h_discrim : 0 ≤ discrim 1 p q := by
    rw [h_discrim]
    positivity
  simp [discrim] at h_discrim
  -- convert the or condition to quadratic inequality
  rw [← l_quadratic_nonneg _ _ _ (by norm_num)]
  constructor
  -- proving α + β equation implies p, q relations
  . rintro ⟨k, h⟩
    -- put α + β in tan (α + β)
    rw [h, tan_add_int_mul_pi, tan_pi_div_three] at h_tan_add
    -- 1 - q is not 0 otherwise √3 = -p / (1 - q) can't happen
    have : 1 - q ≠ 0 := by
      by_contra h'
      simp [h'] at h_tan_add
    -- so we get √3 * (1 - q) = -p
    field_simp at h_tan_add
    -- pluggin in p = √3 * (q - 1) in the discriminant gives us the quadratic 0 ≤ (q - 1 / 3) * (q - 3)
    rw [← neg_sq, ← h_tan_add] at h_discrim
    ring_nf at h_discrim
    simp at h_discrim
    and_intros <;> linarith
  -- proving p, q relations imply α + β value
  . rintro ⟨h1, h2⟩
    -- 1 - q and q - 1 are not 0 due to 0 ≤ (q - 1 / 3) * (q - 3)
    have : 1 - q ≠ 0 := by
      by_contra h'
      have : q = 1 := by linarith
      rw [this] at h1
      norm_num at h1
    have : q - 1 ≠ 0 := by
      by_contra h'
      have : 1 - q = 0 := by linarith
      contradiction
    -- plug in p in tan add formula
    replace h_tan_add : tan (α + β) = (q - 1) * √3 / (q - 1) := by
      rw [← h2]
      rw [h_tan_add]
      field_simp
      ring
    -- so tan (α + β) = tan (π / 3)
    convert_to tan (α + β) = tan (π / 3) at h_tan_add
    . field_simp
    -- now write α + β as r + k * π by lemma, this k is the k in target and r is π / 3
    obtain ⟨k, r, hk, hr_lb, hr_ub⟩ := l_exists_in_period (α + β)
    use k
    convert hk
    -- to show r = π / 3, write α + β as r + k * π in tan, then remove the k * π
    rw [hk, tan_add_int_mul_pi] at h_tan_add
    -- show that - π / 2 < r as, r = π / 2 means tan (α + β) = 0, not possible
    replace hr_lb : - π / 2 < r := by
      apply lt_of_le_of_ne hr_lb
      by_contra hr
      rw [← hr, neg_div, tan_neg] at h_tan_add
      simp at h_tan_add
      have : 0 < √3 := by positivity
      linarith
    -- now we use injectivity of tan in (-π / 2, π / 2)
    apply Real.tan_inj_of_lt_of_lt_pi_div_two <;> linarith