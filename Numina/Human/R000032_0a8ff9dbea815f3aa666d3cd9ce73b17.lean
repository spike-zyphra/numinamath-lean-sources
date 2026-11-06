import Mathlib

open Int

/-- Auxiliary lemma : if $x\equiv k \pmod{16}$, then $\( 9x^{2} + 29x + 62 \) \equiv \( 9k^{2} + 29k + 62 \) \pmod{16}$.  -/
lemma aux (x : ℤ) (h : x ≡ k [ZMOD 16]) :
  9 * x ^ 2 + 29 * x + 62 ≡ 9 * k ^ 2 + 29 * k + 62 [ZMOD 16] := by
    refine Int.ModEq.add ?_ (Int.ModEq.refl 62)
    exact Int.ModEq.add (Int.ModEq.mul (Int.ModEq.refl 9) (ModEq.pow 2 h))
      (ModEq.mul (ModEq.refl 29) h)

/-- Auxiliary lemma : if $k = x \% 16$, then $x \equiv k \pmod{16}$. -/
lemma cast_aux {k x : ℤ} : k = x % 16 → x ≡ k [ZMOD 16] := by
  intro h; have : k % 16 = x % 16 := by rw [h]; simp
  tauto

/-- For which integer values of $\( x \)$ is the number $\( 9x^{2} + 29x + 62 \)$ divisible by 16?-/
theorem number_theory_4060 (x : ℤ) : 9 * x ^ 2 + 29 * x + 62 ≡ 0 [ZMOD 16] ↔
  x ≡ 5 [ZMOD 16] ∨ x ≡ 6 [ZMOD 16] := by
    constructor <;> intro h
    · have h1 : x % 16 < 16 := by refine Int.emod_lt_of_pos x (by linarith)
      have h2 : 0 ≤ x % 16 := by refine Int.emod_nonneg x (by simp)
      set m := x % 16 with hm
      -- Discuss the value of $x \% 16$.
      interval_cases m <;> have := h.symm.trans <| aux x <| cast_aux hm <;>
        norm_num [modEq_iff_dvd] at this
      · have hm : x ≡ 5 [ZMOD 16] := hm.symm
        exact Or.inl hm
      · have hm : x ≡ 6 [ZMOD 16] := hm.symm
        exact Or.inr hm
    · -- Necessity.
      rcases h with hm | hm
      · have h3 := aux x hm
        simp at h3
        exact h3.trans (by rw [modEq_iff_dvd]; norm_num)
      · have h3 := aux x hm
        simp at h3
        exact h3.trans (by rw [modEq_iff_dvd]; norm_num)
