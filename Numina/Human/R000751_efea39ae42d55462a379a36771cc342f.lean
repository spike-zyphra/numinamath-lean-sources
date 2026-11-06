import Mathlib

open Set
theorem algebra_14677 :
{(a, b) : ℤ × ℤ | a^2 + b^2 < 16 ∧ a^2 + b^2 < 8 * a ∧ a^2 + b^2 < 8 * b}.ncard = 6 := by
  -- an auxiliary lemma : for any number $a, b$, if $a^2 + b^2 < 16$, $-4 < a < 4 and -4 < b < 4$.
  have aux {a b : ℤ} (h : a^2 + b^2 < 16) : a ∈ Ioo (-4) 4 ∧ b ∈ Ioo (-4) 4 := by
    by_contra! h1
    by_cases anot : a ∉ Ioo (-4) 4
    · simp at anot
      by_cases age : -4 < a
      · have := anot age
        nlinarith
      · nlinarith
    have := h1 (by tauto)
    simp at this
    by_cases bge : -4 < b
    · have := this bge
      nlinarith
    · nlinarith
  -- Because a^2 + b^2 < 16 ∧ a^2 + b^2 < 8 * a ∧ a^2 + b^2 < 8 * b, we have $0 < a < 4$ and $0 < b <4$.
  -- After checking, the required set is {(1, 1), (2, 2), (1, 2), (2, 1), (3, 2), (2, 3)}.
  have : {(a, b) : ℤ × ℤ | a^2 + b^2 < 16 ∧ a^2 + b^2 < 8 * a ∧ a^2 + b^2 < 8 * b}
    = {(1, 1), (2, 2), (1, 2), (2, 1), (3, 2), (2, 3)} := by
    ext x
    simp
    constructor
    · intro ⟨h1, h2, h3⟩
      replace h2 : (x.1 - 4)^2 + x.2^2 < 16 := by nlinarith
      replace h3 : x.1^2 + (x.2 - 4)^2 < 16 := by nlinarith
      have h1' := aux h1
      have h2' := aux h2
      have h3' := aux h3
      have h4 : x.1 ∈ Ioo 0 4 ∧ x.2 ∈ Ioo 0 4 := by simp_all
      simp at h4
      obtain ⟨⟨x1gt, x1lt⟩, ⟨x2gt, x2lt⟩⟩ := h4
      simp [Prod.eq_iff_fst_eq_snd_eq]
      interval_cases x.1 <;> interval_cases x.2 <;> simp at h1 h2 h3 <;> tauto
    · intro h
      rcases h with h | h | h | h | h | h <;> simp [h]
  -- So there are $\boxed{6}$ ordered pairs meet the condition.
  rw [this]
  have : ({(1, 1), (2, 2), (1, 2), (2, 1), (3, 2), (2, 3)} : Finset (ℤ × ℤ)).card = 6 := by
    native_decide
  convert this
  rw [Set.ncard_eq_toFinset_card _ ]
  simp
