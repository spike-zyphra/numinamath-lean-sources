import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_197588 :
  IsGreatest {x | ∃ a b c d : ℝ, x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a ∧
    a ∈ Icc (-9.5) 9.5 ∧ b ∈ Icc (-9.5) 9.5 ∧ c ∈ Icc (-9.5) 9.5 ∧ d ∈ Icc (-9.5) 9.5} 380 := by
  constructor 
  · -- Show 380 is in the set
    use -9.5, 9.5, -9.5, 9.5
    norm_num [mem_Icc]
    <;> ring
  · -- Show that for any element x in the set, x <= 380
    rintro x ⟨a, b, c, d, h_eq, ha, hb, hc, hd⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 9.5), sq_nonneg (b - 9.5), sq_nonneg (c + 9.5), sq_nonneg (d - 9.5),
          sq_nonneg (a - 9.5), sq_nonneg (b + 9.5), sq_nonneg (c - 9.5), sq_nonneg (d + 9.5)]