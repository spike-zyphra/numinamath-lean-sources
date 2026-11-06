import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_289164 {a : ℝ} (ha : a > 1) (f : ℝ → ℝ)
  (hf : ∀ x, f x = (a ^ x - 1) / (a ^ x + 1)) :
  Odd f ∧ StrictMono f ∧ range f = Ioo (-1) 1 := by

  constructor
  · -- Show f is odd
    unfold Odd
    use fun x => -1 / (a ^ x + 1)
    funext x
    rw [hf]
    field_simp
    <;> ring

  constructor
  · -- Show f is strictly increasing
    intro x y hxy
    have h1 : x < y := hxy
    have h2 : f x = (a ^ x - 1) / (a ^ x + 1) := hf x
    have h3 : f y = (a ^ y - 1) / (a ^ y + 1) := hf y
    rw [h2, h3]
    have h4 : a ^ x > 0 := by positivity
    have h5 : a ^ y > 0 := by positivity
    have h6 : a ^ x < a ^ y := by
      apply Real.rpow_lt_rpow_of_exponent_lt
      · linarith
      all_goals linarith
    have h7 : (a ^ x - 1) / (a ^ x + 1) < (a ^ y - 1) / (a ^ y + 1) := by
      apply (div_lt_div_iff (by positivity) (by positivity)).mpr
      have h8 : (a ^ x - 1) * (a ^ y + 1) < (a ^ y - 1) * (a ^ x + 1) := by
        have h9 : (a ^ x - 1) * (a ^ y + 1) - ((a ^ y - 1) * (a ^ x + 1)) < 0 := by
          have h9 : (a ^ x - 1) * (a ^ y + 1) - ((a ^ y - 1) * (a ^ x + 1)) = 2 * (a ^ x - a ^ y) := by
            ring_nf
          have h10 : 2 * (a ^ x - a ^ y) < 0 := by
            have h11 : a ^ x - a ^ y < 0 := by linarith
            linarith
          linarith [h9, h10]
        linarith
      linarith
    linarith

  · -- Show that range f = Ioo (-1) 1
    ext y
    simp only [mem_range, mem_setOf_eq, mem_Ioo]
    constructor
    · -- First direction: y in range f implies y in (-1, 1)
      rintro ⟨x, hx⟩
      rw [hf x] at hx
      have h10 : a ^ x > 0 := by positivity
      have h11 : -1 < (a ^ x - 1) / (a ^ x + 1) := by
        have h10 : a ^ x > 0 := by positivity
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith
      have h12 : (a ^ x - 1) / (a ^ x + 1) < 1 := by
        have h10 : a ^ x > 0 := by positivity
        apply (div_lt_iff₀ (by linarith)).mpr
        nlinarith
      have h13 : -1 < y := by linarith [h11, hx]
      have h14 : y < 1 := by linarith [h12, hx]
      constructor <;> linarith

    · -- Second direction: y in (-1, 1) implies y in range f
      intro ⟨hy1, hy2⟩
      use Real.logb a ((1 + y) / (1 - y))
      rw [hf]
      have h15 : a ^ (Real.logb a ((1 + y) / (1 - y))) = (1 + y) / (1 - y) := by
        rw [Real.rpow_logb]
        all_goals
          have h10 : (1 - y) > 0 := by linarith
          have h11 : (1 + y) > 0 := by linarith
          have h12 : (1 + y) / (1 - y) > 0 := by apply div_pos; all_goals linarith
          all_goals
            try linarith
      simp [h15]
      have h17 : (1 - y) > 0 := by linarith
      have h18 : (1 + y) > 0 := by linarith
      field_simp [(show (1 - y) ≠ 0 by linarith)] <;> ring_nf