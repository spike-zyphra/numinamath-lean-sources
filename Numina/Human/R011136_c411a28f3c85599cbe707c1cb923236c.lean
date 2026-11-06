import Mathlib

open Real Set
open scoped Real

namespace calculus_7314

lemma sin_eq_one_div_two_iff (x : ℝ) : sin x = 1 / 2 ↔
    ∃ n : ℤ, 2 * (n : ℝ) * π + π / 6 = x ∨ 2 * (n : ℝ) * π + 5 * π / 6 = x := by
  sorry

/- The solutions to $\sin x = 0$ are $x = 0,$ $x = \pi,$ and $x = 2 \pi.$ -/
lemma sin_eq_zero_iff' (x : ℝ) : x ∈ Icc 0 (2 * π) ∧ sin x = 1 / 2 ↔ x = π / 6 ∨ x = 5 * π / 6 := by
  sorry

/- The solutions to $\sin x = \frac{1}{2}$ are $x = \frac{\pi}{6}$ and $x = \frac{5 \pi}{6}.$ -/
lemma sin_eq_one_div_two_iff' (x : ℝ) : x ∈ Icc 0 (2 * π) ∧ sin x = 0 ↔ x = 0 ∨ x = π ∨ x = 2 * π  := by
  simp_rw [sin_eq_zero_iff]
  simp only [mem_Icc]
  constructor
  · intro h
    sorry
  · intro h
    constructor
    rcases h with rfl | rfl | rfl
    on_goal 4 =>
      rcases h with rfl | rfl | rfl
      · use 0
        simp
      · use 1
        simp
      · use 2
        simp
    all_goals constructor
    all_goals linarith [pi_pos]


end calculus_7314

open calculus_7314

/- Determine the number of solutions to
\[2\sin^3 x - 5 \sin^2 x + 2 \sin x = 0\]in the range $0 \le x \le 2 \pi.$ -/
theorem calculus_7314 (f : ℝ → ℝ) (hf : f = λ x => 2 * sin x ^ 3 - 5 * sin x ^ 2 + 2 * sin x)
    (a b : ℝ) (ha : a = 0) (hb : b = 2 * π) :
    {x ∈ Icc a b | f x = 0}.ncard = 5 := by
  subst a b
  -- The given equation factors as [\sin x (2 \sin x - 1)(\sin x - 2) = 0,]
  have h1 (x : ℝ) : f x = 0 ↔ sin x * (2 * sin x - 1) * (sin x - 2) = 0 := by
    rw [hf]
    ring_nf
  -- so $\sin x = 0,$ $\sin x = \frac{1}{2},$ or $\sin x = 2.$
  have h2 (x : ℝ) : sin x * (2 * sin x - 1) * (sin x - 2) = 0 ↔ sin x = 0 ∨
      sin x = 1 / 2 ∨ sin x = 2 := by
    simp only [mul_eq_zero]
    field_simp
    nth_rw 1 [sub_eq_zero, mul_comm (sin x) 2]
    rw [sub_eq_zero ]
    exact or_assoc
  -- The equation $\sin x = 2$ has no solutions.
  have h3 (x : ℝ) : sin x = 2 ↔ False := by
    simp
    linarith [sin_le_one x]
  simp_rw [h3] at h2
  simp_rw [h2] at h1
  simp only [or_false] at h1
  simp_rw [h1, and_or_left]
  -- The solutions to $\sin x = 0$ are $x = 0,$ $x = \pi,$ and $x = 2 \pi.$ 
  simp_rw [sin_eq_zero_iff']
  -- The solutions to $\sin x = \frac{1}{2}$ are $x = \frac{\pi}{6}$ and $x = \frac{5 \pi}{6}.$
  simp_rw [sin_eq_one_div_two_iff']
  -- Thus, the solutions are $0,$ $\pi,$ $2 \pi,$ $\frac{\pi}{6},$ and $\frac{5 \pi}{6},$ for a total of $\boxed{5}$ solutions
  have h5 : {x | (x = 0 ∨ x = π ∨ x = 2 * π) ∨ x = π / 6 ∨ x = 5 * π / 6} =
    {0 , π, 2 * π, π / 6, 5 * π / 6} := by
    ext t
    constructor
    · intro h
      simp only [mem_setOf_eq, or_assoc] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      all_goals simp
    · intro h
      simp only [mem_insert_iff, mem_singleton_iff] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      all_goals simp
  rw [h5]
  rw [← Set.Nat.card_coe_set_eq]
  simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, toFinset_insert, toFinset_singleton]
  have h6 : [0, π, 2 * π, π / 6, 5 * π / 6].Nodup := by
    simp
    split_ands
    <;> nlinarith [pi_pos]
  simp_all

