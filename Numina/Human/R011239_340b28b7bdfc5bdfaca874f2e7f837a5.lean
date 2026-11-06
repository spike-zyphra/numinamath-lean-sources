import Mathlib

/- 53. (USA 2) Find all pairs of integers $a$ and $b$ for which  $$ 7 a+14 b=5 a^{2}+5 a b+5 b^{2} $$ -/
theorem algebra_23630 (a b : ℤ) :
7 * a + 14 * b = 5 * a^2 + 5 * a * b + 5 * b^2 
↔
(a = -1 ∧ b = 3) ∨ (a = 0 ∧ b = 0) ∨ (a = 1 ∧ b = 2) := by

  constructor

  --From left to right. We rewrite the given equation to a quadratic equation of b.
  intro h

  have eq : 5 * (b*b) + (5*a-14)*b + (5*a^2 - 7*a) = 0 := by linarith

  rw [quadratic_eq_zero_iff_discrim_eq_sq (show (5:ℤ) ≠ 0 by omega) b ] at eq
  unfold discrim at eq

  --Then, the discri must be non-negative, so 75a^2 ≤ 196 and hence a = 1, 0, or -1.
  have diseq : (5 * a - 14) ^ 2 - 4 * 5 * (5 * a ^ 2 - 7 * a) = 196 - 75 * a^2 := by ring
  rw [diseq] at eq
  have disnneg : 0 ≤ 196 - 75 * a ^ 2 := by 
    have : 0 ≤ (2 * 5 * b + (5 * a - 14)) ^ 2 := by exact sq_nonneg (2 * 5 * b + (5 * a - 14))
    linarith
  have ale1  : a ≤ 1 := by nlinarith
  have agem1 : -1≤ a := by nlinarith

  --We check each case and get the value of b.
  interval_cases a <;>
  simp at eq h ⊢

  have : (121:ℤ) = 11^2 := by norm_num
  rw [this] at eq
  have : 11 = 10*b+(-19) ∨ 11 = -(10*b+(-19)) := by exact sq_eq_sq_iff_eq_or_eq_neg.mp eq
  rcases this with h | h <;>
  omega

  have : (196:ℤ) =  14^2 := by norm_num
  rw [this] at eq
  have : 14 = (10*b + (-14)) ∨ 14 = - (10*b + (-14)) := by exact sq_eq_sq_iff_eq_or_eq_neg.mp eq
  rcases this with h | h <;>
  omega

  have : (121:ℤ) = 11^2 := by norm_num
  rw [this] at eq
  have : 11 = 10*b+(-9) ∨ 11 = -(10*b+(-9)) := by exact sq_eq_sq_iff_eq_or_eq_neg.mp eq
  rcases this with h | h <;>
  omega


  
  --For the other direction, simple calculation.
  intro h
  obtain ⟨ae,be⟩ | ⟨ae,be⟩ | ⟨ae,be⟩ := h <;>
  simp [ae,be] 