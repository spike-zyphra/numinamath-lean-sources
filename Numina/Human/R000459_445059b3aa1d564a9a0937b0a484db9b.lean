import Mathlib

open Real

/- Let $a,$ $b,$ $c$ be three distinct positive real numbers such that $a,$ $b,$ $c$ form a geometric sequence, and
$$\log_c a, \ \log_b c, \ \log_a b$$form an arithmetic sequence.  Find the common difference of the arithmetic sequence. -/
theorem algebra_10880
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdist : a ≠ b ∧ b ≠ c ∧ a ≠ c)
    (hge : ∃ r, b = a * r ∧ c = b * r)
    (hlog : ∃ d, logb b c  - logb c a = d ∧ logb a b - logb b c = d) :
    logb b c  - logb c a = 3 / 2 := by

  obtain ⟨r, hbr, hcr⟩ := hge
  obtain ⟨d, hd1, hd2⟩ := hlog
  have hrpos : r > 0 := by by_contra!; linarith [Linarith.mul_nonpos this ha]

  -- auxiliary lemma
  have logb_one' {b : ℝ} : logb b 1 = 0 := by simp [logb]
  have logb_one_left' {x : ℝ} : logb 1 x = 0 := by simp only [← log_div_log, log_one, div_zero]

  have hcne1 : c ≠ 1 := by
    by_contra! h_contra
    rw [h_contra, logb_one', logb_one_left', sub_self] at hd1
    rw [← hd1, h_contra, logb_one, sub_zero] at hd2
    obtain ⟨_, _, _⟩ := hdist
    rcases logb_eq_zero.mp hd2 with h | h | h | h | h | h
    any_goals linarith
    any_goals simp_all

  have hc1 : log c ≠ 0 := by
    by_contra!
    rcases log_eq_zero.mp this with h | h | h
    any_goals linarith
    contradiction


  -- Since $a,$ $b,$ $c$ form a geometric sequence, $b = \sqrt{ac}.$
  have r1 : b = √ (a * c) := by
    simp only [hbr, hcr]
    ring_nf
    field_simp

  -- Then the three logarithms become $\log_c a, \ \log_{\sqrt{ac}} c, \ \log_a \sqrt{ac}.$
  rw [r1] at hd1 hd2

  -- Let $x = \log_c a.$
  set x := logb c a with hx

  -- Then by the change-of-base formula, $\log_{\sqrt{ac}} c = \frac{\log_c c}{\log_c \sqrt{ac}} = \frac{1}{\frac{1}{2} \log_c ac} = \frac{2}{\log_c a + \log_c c} = \frac{2}{x + 1}$,
  have r2 : logb (√ (a * c)) c = 2 / (x + 1) := by
    rw [logb] at hx
    rw [logb, log_sqrt, log_mul, ← div_mul, mul_comm, mul_div, hx]
    apply_fun fun t => 2⁻¹ * t
    ring_nf
    rw [← div_eq_mul_inv, inv_eq_one_div, (mul_div_mul_right 1 (1 + log a * (log c)⁻¹) hc1).symm]
    . field_simp
    any_goals linarith
    . apply mul_right_injective₀
      norm_num
    . apply le_of_lt
      exact mul_pos ha hc

  -- and $\log_a \sqrt{ac} = \frac{1}{2} \log_a ac = \frac{\log_c ac}{2 \log_c a} = \frac{\log_c a + \log_c c}{2 \log_c a} = \frac{x + 1}{2x}$.
  have r3 : logb a (√ (a * c)) = (x + 1) / (2 * x) := by
    rw [logb] at hx
    conv => rhs; apply (mul_div_mul_right _ _ hc1).symm
    rw [logb, log_sqrt, log_mul, div_div, hx, add_mul, div_mul_cancel₀ _ hc1, mul_assoc, div_mul_cancel₀ _ hc1, one_mul]
    any_goals linarith
    apply le_of_lt
    exact mul_pos ha hc

  -- Let $d$ be the common difference, so $d = \frac{2}{x + 1} - x = \frac{x + 1}{2x} - \frac{2}{x + 1}$.
  simp only [← hx, r2, r3] at hd1 hd2

  -- corner cases
  have ⟨hx1, hx2⟩ : x + 1 ≠ 0 ∧ 2 * x ≠ 0 := by
    constructor
    . by_contra! h_contra
      simp [h_contra] at hd1 hd2
      linarith
    . by_contra! h_contra
      simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h_contra
      simp [h_contra] at hd1 hd2
      linarith

  -- Then $4x - 2x^2 (x + 1) = (x + 1)^2 - 4x$, which simplifies to $2x^3 + 3x^2 - 6x + 1 = 0.$  This factors as $(x - 1)(2x^2 + 5x - 1) = 0.$
  have tmp : 2 / (x + 1) - x = (x + 1) / (2 * x) - 2 / (x + 1) := by rw [hd1, hd2]
  apply_fun fun t => t * (x + 1) at tmp
  rw [sub_mul, div_mul_cancel₀ _ hx1, sub_mul, div_mul_cancel₀ _ hx1] at tmp
  apply_fun fun t => t * (2 * x) at tmp
  rw [sub_mul, sub_mul, div_mul, div_mul_comm, ← div_mul, div_self hx2] at tmp
  have : (x - 1) * (2 * x ^ 2  + 5 * x - 1) = 0 := by linarith

  rcases mul_eq_zero.mp this with h | h

  -- If $x = 1,$ then $\log_c a = 1,$ so $a = c.$  But $a$ and $c$ are distinct,
  . have : logb c a = 1 := by linarith
    have : a = c := by
      have := (logb_eq_iff_rpow_eq hc hcne1 ha).mp this
      norm_cast at this
      rw [pow_one] at this
      exact this.symm
    obtain ⟨h1, h2, h3⟩ := hdist
    contradiction

  -- so $2x^2 + 5x - 1 = 0,$ so $x^2 = \frac{1 - 5x}{2}.$ Then $d = \frac{2}{x + 1} - x = \frac{2 - x^2 - x}{x + 1} = \frac{2 - \frac{1 - 5x}{2} - x}{x + 1} = \frac{3x + 3}{2(x + 1)} = \boxed{\frac{3}{2}}.$
  . rw [r1, r2, hd1]
    have : x ^ 2 = (1 - 5 * x) / 2 := by linarith
    calc
      _ = 2 / (x + 1) - x := by rw [hd1.symm]
      _ = (2 - x ^ 2 - x) / (x + 1) := by field_simp; ring_nf
      _ = (2 - (1 - 5 * x) / 2 - x) / (x + 1) := by rw [this]
      _ = (3 * (x + 1)) / (2 * (x + 1)) := by field_simp; ring_nf
      _ = 3 / 2 := by field_simp; ring_nf
