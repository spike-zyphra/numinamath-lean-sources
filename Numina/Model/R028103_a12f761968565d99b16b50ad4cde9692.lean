import Mathlib

theorem number_theory_276267 (a b : ℝ) (ha : ∃ p q : ℤ, a = p / q) (hb : Irrational b) :
    ¬ ∃ p q : ℤ, a + b = p / q := by 
  rintro ⟨p, q, h_eq⟩ 
  rcases ha with ⟨p₁, q₁, ha₁⟩
  have h2 : b = (p / q : ℝ) - (p₁ / q₁ : ℝ) := by
    have h : (a : ℝ) = (p₁ / q₁ : ℝ) := by simpa using ha₁
    linarith
  rw [h2] at hb
  norm_cast at hb ⊢
  <;> norm_num [Int.cast_div, Rat.cast_div, mul_add, mul_sub, add_mul, sub_mul, mul_add, mul_sub, add_mul, sub_mul] at hb ⊢
  <;> norm_cast at hb ⊢
  <;> norm_num [Int.cast_div, Rat.cast_div, mul_add, mul_sub, add_mul, sub_mul, mul_add, mul_sub, add_mul, sub_mul] at hb ⊢
  <;> norm_cast at hb ⊢
  all_goals norm_cast at hb ⊢
  <;> norm_cast at hb ⊢
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }
  <;> try { contradiction }
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }
  all_goals norm_cast at hb ⊢
  <;> try { contradiction }
  <;> try { native_decide }