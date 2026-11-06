import Mathlib

/-Find the number of different pairs of positive integers  $(a,b)$  for which  $a+b\le100$  and \[\dfrac{a+\frac{1}{b}}{\frac{1}{a}+b}=10\]-/
theorem number_theory_8950_1: {(a, b) : ℤ × ℤ |  0 < a ∧ 0 < b ∧ a + b ≤ 100
∧ (a + 1/(b : ℚ)) / (1 / (a : ℚ) + b) = 10} =
{(a, b) : ℤ × ℤ | a = 10 * b ∧ b ≤ 9 ∧ 0 < b} := by
-- Introduce variables and assumptions, break "iff"
  ext x; simp; constructor
  · rintro ⟨h1, h2, h12, heq⟩
-- Simplify assumptions to get $x.1=10*x.2$
    field_simp at heq; rw [← mul_assoc, mul_comm, add_comm] at heq
    nth_rw 2 [mul_comm] at heq; apply mul_right_cancel₀ at heq
    norm_cast at heq
-- Plug in $x.1=10*x.2$ to h12 and show that $x.2≤9$
    rw [heq] at h12; ring_nf at h12
    constructor; assumption; constructor
    · by_contra h'; push_neg at h'
      have := @Int.mul_lt_mul_of_pos_right 9 x.2 11 h' (show (0:ℤ)<11 by norm_num)
      linarith; 
    assumption; by_contra h''
    have t1 : 1 + (x.2 : ℚ)*(x.1 : ℚ) = ↑(1 + x.2 * x.1) := by simp
    rw [t1, Rat.intCast_eq_zero] at h''
    have t2 := Int.mul_pos h2 h1
    linarith
  rintro ⟨h1, h2, h3⟩; simp_all; constructor; linarith
  rw [div_eq_iff, mul_add]; ring
  have : 1 ≤ (x.2:ℚ) := by norm_cast
  have : (x.2:ℚ) ≤ (x.2:ℚ)⁻¹ * 10⁻¹ + (x.2:ℚ) := by simp; linarith
  linarith

/-Find the number of different pairs of positive integers  $(a,b)$  for which  $a+b\le100$  and \[\dfrac{a+\frac{1}{b}}{\frac{1}{a}+b}=10\]-/
theorem number_theory_8950_2 :
{(a, b) : ℤ × ℤ | a = 10 * b ∧ b ≤ 9 ∧ 0 < b}.ncard = 9 := by
-- Let the projection to the second coordinate be $p2$
  let p2 (x : ℤ × ℤ) : ℤ := x.2
-- Prove that $p2$ is injective on the solution set
  have inj : Set.InjOn p2 {(a, b) : ℤ × ℤ | a = 10 * b ∧ b ≤ 9 ∧ 0 < b} := by
    intro P hP Q hQ hPQ; rw [Prod.ext_iff]; simp_all [p2]
-- Prove that the image of the solution set under $p2$ is Set.Icc 1 9
  have img : p2 '' {(a, b) : ℤ × ℤ | a = 10 * b ∧ b ≤ 9 ∧ 0 < b} = Set.Icc 1 9 := by
    ext y; simp; constructor
    · intro; constructor; linarith; linarith
    intro; constructor; linarith; linarith
-- Count the numbers in Set.Icc 1 9 and prove the final goal
  rw [← Set.ncard_image_of_injOn inj, img]
  rw [Set.ncard_eq_toFinset_card']; simp