import Mathlib

open Polynomial

/- The roots of the quadratic equation $a x^{2}+b x+c=0$ with integer coefficients are distinct and both lie between 0 and 1. Show that if $a$ is positive, then it is at least 5. -/
theorem algebra_150704 {a b c : ℤ} (h_a_pos : 0 < a) (hroots : ∃ x y : ℝ, x ≠ y ∧ a*(x*x) + b*x + c = 0 ∧ a*(y*y) + b*y + c = 0 ∧ x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1) :
    5 ≤ a := by
  obtain ⟨x, y, h_neq, h_x_root, h_y_root, h_x_range, h_y_range⟩ := hroots

  -- without loss of generality, we can assume that x is the smaller root, and y the larger
  wlog h_lt : x < y
  · apply (this h_a_pos y x ) <;> try assumption
    case h_neq => 
      symm
      exact h_neq
    case h_lt => 
      simp at h_lt
      apply lt_of_le_of_ne h_lt
      symm
      exact h_neq

  -- By the abc-formula, we know that x = (-b - √(b^2 - 4*a*c))/(2*a) and y = (-b + √(b^2 - 4*a*c))/(2*a)
  have h_discrim_nonneg : 0 ≤ discrim (a:ℝ) b c := by
    rw [discrim_eq_sq_of_quadratic_eq_zero h_x_root, sq]
    apply mul_self_nonneg
  have h_discrim_sq : discrim (a:ℝ) b c = √(discrim a b c) * √(discrim a b c) := by
    rw [Real.mul_self_sqrt]
    apply h_discrim_nonneg
  have hx : x = (-b - √(discrim a b c))/(2*a) ∨ x = (-b + √(discrim a b c))/(2*a) := by
    cases (quadratic_eq_zero_iff (by norm_cast; omega) h_discrim_sq x).mp h_x_root
    case inl h =>
      right
      exact h
    case inr h =>
      left
      exact h
  have hy : y = (-b - √(discrim a b c))/(2*a) ∨ y = (-b + √(discrim a b c))/(2*a) := by
    cases (quadratic_eq_zero_iff (by norm_cast; omega) h_discrim_sq y).mp h_y_root
    case inl h => 
      right
      exact h
    case inr h =>
      left
      exact h
  have : x = (-b - √(discrim a b c))/(2*a) ∧ y = (-b + √(discrim a b c))/(2*a) := by
    cases hx <;> cases hy
    case inl.inl h1 h2 => rw [h1,h2] at h_neq ; contradiction
    case inr.inr h1 h2 => rw [h1,h2] at h_neq ; contradiction
    case inl.inr => trivial
    case inr.inl hx hy =>
      rw [hx,hy] at h_lt
      apply not_le_of_lt at h_lt
      exfalso
      apply h_lt
      apply div_le_div_of_nonneg_right
      case hab =>
        rw [sub_eq_add_neg]
        apply add_le_add_left
        apply Real.neg_sqrt_le_of_sq_le
        rw [sq, ← h_discrim_sq]
      case hc =>
        norm_cast
        omega
  obtain ⟨hx,hy⟩ := this
  
  -- Because there are two distinct roots, the discriminant must be strictly positive
  have h_discrim_pos : 0 < discrim (a:ℝ) b c := by
    apply (lt_of_le_of_ne h_discrim_nonneg)
    intro h
    apply h_neq
    rw [hx,hy]
    rw [← h]
    simp

  -- we can derive that x*y = c/a, and 0<x*y<1
  -- as a result, c is positive, and c<a
  have : x*y = c/a := by
    rw [hx,hy]
    ring_nf
    rw [Real.sq_sqrt h_discrim_nonneg]
    unfold discrim
    field_simp
    ring
  obtain ⟨h_x_pos, h_x_lt_1⟩ := Set.mem_Ioo.mp h_x_range
  obtain ⟨h_y_pos, h_y_lt_1⟩ := Set.mem_Ioo.mp h_y_range
  have h_c_pos : 0 < c := by
    rify
    have ha : 0 < (a:ℝ) := by norm_cast
    apply (div_pos_iff_of_pos_right ha).mp
    rw [← this]
    apply mul_pos h_x_pos h_y_pos
  have h_c_lt_a : c < a := by
    rify
    suffices : (c:ℝ)/a < 1
    · have ha: 0 < (a:ℝ) := by norm_cast
      apply (div_lt_div_iff_of_pos_right ha).mp
      rw [div_self]
      assumption
      norm_cast
      omega
    rw [← this]
    apply mul_lt_one_of_nonneg_of_lt_one_left <;> linarith

  -- from 0<x, we can derive that b>0
  have h_b_pos : b < 0 := by
    rify
    rw [hx] at h_x_pos
    have hb : 0 < 2 * (a:ℝ) := by norm_cast; linarith
    apply (div_pos_iff_of_pos_right hb).mp at h_x_pos
    have : b < - √(discrim a b c) := by linarith
    apply lt_trans this
    apply neg_lt_zero.mpr
    apply Real.sqrt_pos.mpr h_discrim_pos
  
  -- because y<1, we can derive √(b^2 -4ac) < 2a+b, and then -a-c < b
  have h: √(b*b - 4*a*c) < 2*a+b := by
    rw [hy] at h_y_lt_1
    unfold discrim at h_y_lt_1
    rw [sq] at h_y_lt_1
    apply (sub_lt_sub_iff_right (b:ℝ)).mp
    field_simp
    have : 0 < 2*(a:ℝ) := by norm_cast; linarith
    apply (div_lt_div_iff_of_pos_right this).mp
    field_simp
    convert h_y_lt_1 using 2
    apply sub_eq_neg_add

  have h_abc : -a-c < b := by
    suffices : -c < a+b
    · linarith
    apply mul_self_lt_mul_self (Real.sqrt_nonneg _) at h
    rw [Real.mul_self_sqrt ?discrim_nonneg] at h
    case discrim_nonneg =>
      unfold discrim at h_discrim_nonneg
      rw [← sq]
      assumption
    have : 0 ≤ 4*a := by linarith
    apply lt_of_mul_lt_mul_left
    case a0 => exact this
    apply lt_of_add_lt_add_left
    case a => exact b*b
    rify
    calc
      _ = (b:ℝ) * ↑b - 4 * ↑a * ↑c := by ring_nf
      _ < (2 * ↑a + ↑b) * (2 * ↑a + ↑b) := h
      _ = b*b + 4 * ↑a * (↑a + ↑b) := by ring_nf

  have h_b_upper : -2*a < b := by
    have : 0 < 2*a + b := by
      rify
      apply lt_trans
      apply Real.sqrt_pos.mpr h_discrim_pos
      unfold discrim
      rw [sq]
      assumption
    linarith

  -- now we can check all four values of a that would make the statement untrue: 1,2,3,4
  -- each has a few options for b and c, and ultimately lead to a contradiction with h_discrim_pos and h_abc
  by_contra h_a
  unfold discrim at h_discrim_pos
  rw [sq] at h_discrim_pos
  interval_cases a
  all_goals interval_cases c
  all_goals interval_cases b
  all_goals simp at h_discrim_pos
  all_goals linarith