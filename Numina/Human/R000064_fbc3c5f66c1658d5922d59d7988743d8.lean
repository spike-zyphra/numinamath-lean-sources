import Mathlib

open Real
open Set

/--Auxiliary lemma : For any integer $t$,
$$
\cos \left( \pi \cdot \cos \left( \frac{\pi}{3} + \pi t \right) \right) = 0
$$ -/
lemma l_1 (t : ℤ) : cos (π * cos (π / 3 + π * t)) = 0 := by
  rw [mul_comm π t, cos_add_int_mul_pi]
  rcases Int.even_or_odd t with h | h
  . rw [Even.neg_one_zpow h]; simp [show π * 2⁻¹ = π / 2 from rfl]
  . rw [Odd.neg_one_zpow h]; simp [show π * 2⁻¹ = π / 2 from rfl]

/--Auxiliary lemma : For any integer $t$,
$$
\cos \left( \pi \cdot \cos \left( \frac{\pi}{3} + \pi t \right) \right) = 0
$$ -/
lemma l_1' (t : ℤ) : cos (π * cos (π / 3 + π * t)) = 0 := by
  by_cases he : Even t
  . obtain ⟨n, rfl⟩ := he
    rw [← two_mul]
    simp; rw [← mul_assoc]
    rw [mul_comm (π * 2), mul_comm π 2]
    rw [cos_add_int_mul_two_pi]
    rw [cos_pi_div_three, mul_div_assoc', mul_one, cos_pi_div_two]
  . obtain ⟨n, rfl⟩ := Int.not_even_iff_odd.mp he
    simp; rw [mul_add, mul_one, add_comm _ π, ← add_assoc, mul_comm 2, mul_comm π (↑n * 2), mul_assoc, cos_add_int_mul_two_pi]
    rw [cos_add_pi, cos_pi_div_three]
    simp; exact cos_pi_div_two

/-- Auxiliary lemma : For any integer $t$,
$$
\sin \left( 2 \pi \sqrt{3} \cdot \sin \left( \frac{\pi}{3} + \pi t \right) \right) = 0$$ -/
lemma l_2 (t : ℤ) : sin (2 * π * √3 * sin (π / 3 + π * t)) = 0 := by
  rw [mul_comm π t, sin_add_int_mul_pi]
  rcases Int.even_or_odd t with h | h
  . rw [Even.neg_one_zpow h, sin_pi_div_three, ← sin_zero, sin_eq_sin_iff]
    use 1; simp; ring_nf; field_simp
  . rw [Odd.neg_one_zpow h, sin_pi_div_three, ← sin_zero, sin_eq_sin_iff]
    use -2; simp; ring_nf; field_simp

/-- Auxiliary lemma : For any integer $t$, $\cos \left( \pi \cdot \cos \left( -\frac{\pi}{3} + \pi t \right) \right) = 0$. -/
lemma l_3 (t : ℤ) : cos (π * cos (-π / 3 + π * t)) = 0 := by
  rw [← l_1 (-t), ← cos_neg (-π / 3 + π * t)]
  simp; ring_nf

/-- Auxiliary lemma : For any integer $t$,
$\sin \left( 2 \pi \sqrt{3} \cdot \sin \left( -\frac{\pi}{3} + \pi t \right) \right) = 0$. -/
lemma l_4 (t : ℤ) : sin (2 * π * √3 * sin (-π / 3 + π * t)) = 0 := by
  set nt : ℤ := -t with hnt
  calc sin (2 * π * √3 * sin (-π / 3 + π * t))
    _ = sin (2 * π * √3 * - sin (π / 3 + π * nt)) := by
      rw [← sin_neg, hnt]; simp; ring_nf
    _ = - sin (2 * π * √3 * sin (π / 3 + π * nt)) := by
      rw [← sin_neg (2 * π * √3 * sin (π / 3 + π * nt))]; ring_nf
  rw [neg_eq_zero]
  apply l_2

/-- Auxiliary lemma : if $a^2 + b^2 = 0$, then $a = 0$ and $b = 0$. -/
lemma l_5 {a b : ℝ} (h : (a ^ 2) + (b ^ 2) = 0) : a = 0 ∧ b = 0:= by
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg a) (sq_nonneg b)).mp h
  exact ⟨pow_eq_zero ha, pow_eq_zero hb⟩


lemma l_6_pre1 {x : ℝ} : (∃ k : ℤ, π / 2 = 2 * k * π + π * cos x) → ∃ k : ℤ, cos x = 1 / 2 + k := by
  rintro ⟨k, hk⟩
  have : π / 2 - 2 * (k : ℝ) * π = π * cos x := by linarith   -- 这里要手动引导到该表达式
  rw [mul_comm π, ← div_eq_iff (ne_of_gt Real.pi_pos)] at this
  rw [show (π / 2 - 2 * (k:ℝ) * π) / π = 1 / 2 - (k:ℝ) * 2 by field_simp; ring] at this
  use (- 2 * k)
  simp [← this]; ring

lemma l_6_pre2 {x : ℝ} : (∃ k : ℤ, π / 2 = 2 * k * π - π * cos x) → ∃ k : ℤ, cos x = 1 / 2 + k := by
  rintro ⟨k, hk⟩
  have : 2 * (k : ℝ) * π - π / 2 = π * cos x := by linarith   -- 这里要手动引导到该表达式
  rw [mul_comm π, ← div_eq_iff (ne_of_gt Real.pi_pos)] at this
  rw [show (2 * (k:ℝ) * π - π / 2) / π = 2 * (k:ℝ) - 1 / 2 by field_simp; ring] at this
  use (2 * k - 1)
  simp [← this]; ring

lemma l_6_pre3 {x : ℝ} : cos (π * cos x) = 0 → ∃ k : ℤ, cos x = 1 / 2 + k := by
  intro h
  rw [← cos_pi_div_two] at h
  rw [cos_eq_cos_iff, exists_or] at h
  exact h.elim l_6_pre1 l_6_pre2

/-- Auxiliary lemma : $\cos \left(\pi \cos x\right) = 0$ implies
  $\sin ^2 x = \frac{3}{4} $ -/
lemma l_6 {x : ℝ} : cos (π * cos x) = 0 → (sin x) ^ 2 = 3 / 4 := by
  intro h_cos
  apply l_6_pre3 at h_cos
  obtain ⟨k, h_cos⟩ := h_cos
  have h_cos_mem : cos x ∈ Icc (-1 : ℝ) 1 := cos_mem_Icc x
  have hk_min : k ≥ -1 := by
    have : (k:ℝ) > -2 := by linarith [h_cos_mem.1]
    norm_cast at this
  have hk_max : (k:ℝ) < 1 := by linarith [h_cos_mem.2]
  norm_cast at hk_max
  interval_cases k; all_goals simp [h_cos, sin_sq]
  ring; ring

/-- Auxiliary lemma : $\sin ^2 x = \frac{3}{4} $ implies that
  $x = \frac {\pi} 3 + \pi \cdot t$ or $x = -\frac {\pi} 3 + \pi \cdot t$. -/
lemma l_7 : (sin x) ^ 2 = 3 / 4 → ∃ t : ℤ, x = π / 3 + π * t ∨ x = -π / 3 + π * t := by
  intro h
  have : |sin x| = |√ 3 / 2| := by
    simp only [← sqrt_sq_eq_abs, h, show (4 : ℝ) = 2 ^ 2 by norm_num, Nat.ofNat_nonneg, sqrt_div,
      sqrt_sq]
    rw [sqrt_sq_eq_abs]
    refine (abs_eq_self.mpr ?_).symm
    rw [div_nonneg_iff]; norm_num
  cases (abs_eq_abs.mp this) with
  | inl h =>
    rw [← sin_pi_div_three, sin_eq_sin_iff] at h
    obtain ⟨k, hk⟩ := h
    cases hk with
    | inl hh => use (-2 * k); simp [hh]; ring_nf; simp
    | inr hh =>
      rw [neg_eq_neg_one_mul, mul_div_assoc]
      use (2 * k + 1)
      simp [hh]; ring_nf; simp
  | inr h =>
    rw [← sin_pi_div_three, ← sin_neg, sin_eq_sin_iff] at h
    obtain ⟨k, hk⟩ := h
    cases hk with
    | inl hh =>
      rw [neg_eq_neg_one_mul, mul_div_assoc', neg_one_mul] at hh
      use (-2 * k); simp [hh]; ring_nf; simp
    | inr hh =>
      symm at hh; rw [sub_eq_iff_eq_add, ← add_comm x, ← sub_eq_iff_eq_add, sub_neg_eq_add] at hh; symm at hh
      use (2 * k + 1)
      simp [hh]; ring_nf; simp

/-- Define the function to be discussed-/
noncomputable def f (x : ℝ) := (cos (π * cos x)) ^ 2 + (sin (2 * π * √ 3 * sin x)) ^ 2

/-- show 0 is the minimum value. -/
theorem f_ge_zero (x : ℝ) : 0 ≤ f x := by
  apply add_nonneg <;> apply sq_nonneg

/-- For which values of $x$ does the expression  $\cos^2(\pi \cos x) + \sin^2\left( \frac{2\pi}{3} \sin x \right)$ attain its minimum value? -/
theorem Calculus_4204 (x : ℝ) : f x = 0 ↔ ∃ t : ℤ, x = π / 3 + π * t ∨ x = -π / 3 + π * t := by
  constructor
  -- Sufficiency
  . intro h_top
    simp only [f] at h_top
    set h0 : cos (π * cos x) = 0 := (l_5 h_top).left
    set constraint_cos : (sin x) ^ 2 = 3 / 4 := l_6 h0
    exact l_7 constraint_cos
  -- necessity
  . rintro ⟨t, h_top⟩
    cases h_top with
    | inl h =>
      simp [f, h, l_1, l_2]
    | inr h =>
      simp [f, h, l_3, l_4]
