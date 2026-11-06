import Mathlib

open Set Real

/- 5. Let the set $A=\left\{x \left\lvert\, \frac{x-1}{x+1}<0\right., B=\{x|| x-b \mid<a\}\right.$,
if “ $a=1$ ” is a sufficient condition for “ $A \cap B \neq \varnothing$ ”, then the range of values
 for $b$ is A. $-2 \leqslant b<0$ B. $0<b \leqslant 2$ C. $-3<b<-1$ D. $-1 \leqslant b<2$ --/
theorem my_favorite_theorem {a b : ℝ} (A B : Set ℝ) (hA : A = {x | (x - 1) / (x + 1) < 0})
    (hB : B = {x | abs (x - b) < a}) : a = 1 → A ∩ B ≠ ∅ → -2 < b ∧ b < 2 := by
  intro ha hin
  -- We have $A = (-1, 1)$
  have A_eq : A = Ioo (-1) 1 := by
    refine ext fun x ↦ ?_
    have (x : ℝ): ¬ ( 1 < x ∧ x + 1 < 0) := by
      intro ⟨h1, h2⟩
      linarith
    simp [hA, mem_setOf_eq, mem_Ioo, div_neg_iff, this]
    nth_rw 2 [And.comm]
    refine and_congr gt_iff_lt ?_
    constructor
    · intro h; linarith
    · intro h; linarith
  -- We have $B = (b - 1 , b + 1)$
  have B_eq : B = Ioo (b - 1) (b + 1) := by
    refine ext fun x ↦ ?_
    simp [hB, ha]
    constructor
    · exact fun h ↦ ⟨sub_lt_of_abs_sub_lt_left h,
        lt_add_of_tsub_lt_right (sub_lt_of_abs_sub_lt_right h)⟩
    · intro ⟨h1, h2⟩
      refine abs_sub_lt_iff.mpr ?_
      simpa [And.comm] using ⟨sub_lt_comm.mp h1, sub_left_lt_of_lt_add h2⟩
  -- $A \cap B = \empty$ exactly impleis $-2 < b < 2$
  simp [A_eq, B_eq, Ioo_inter_Ioo, Ioo_eq_empty_iff] at hin
  constructor
  · linarith [hin.2.1]
  · linarith [hin.1]
