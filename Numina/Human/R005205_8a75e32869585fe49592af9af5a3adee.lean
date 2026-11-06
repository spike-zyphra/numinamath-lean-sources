import Mathlib

/-

Determine the smallest positive integer $q$ with the following property:

for every integer $m$ with $1 \leqslant m \leqslant 1006$, there exists an integer $n$ such that

$$
\frac{m}{1007} q < n <\frac{m+1}{1008} q .
$$ -/
theorem number_theory_606271 :
    IsLeast {q : ℤ | 0 < q ∧ ∀ m ∈ Finset.Icc (1 : ℤ) 1006, ∃ n : ℤ, (m : ℚ) / 1007 * q < n ∧ n < (m + 1 : ℚ) / 1008 * q} 2015 := by
  -- Break the goal into two parts.
  simp [IsLeast, lowerBounds]
  refine ⟨?_, ?_⟩
  . -- Show that q = 2015 works.
    intro m hm₁ hm₂
    -- Simply take n = 2m+1.
    refine ⟨2 * m + 1, ?_, ?_⟩
    . -- Show that m / 1007 * 2015 < 2 * m + 1.
      field_simp
      rw [div_lt_iff₀]
      ring_nf
      norm_cast
      omega
      norm_num
    . -- Show that 2 * m + 1 < (m + 1) / 1008 * 2015.
      field_simp
      rw [lt_div_iff₀]
      ring_nf
      norm_cast
      omega
      norm_num
  . -- Show that q ≥ 2015.
    intro q hq h
    -- Assume q < 2015 by contradiction.
    by_contra! h₀
    -- Substitute m = 1006 at h.
    obtain ⟨n, h₁, h₂⟩ := h 1006 (by norm_num) (by norm_num)
    clear h
    -- Show that n < q.
    have h₃ : (n : ℚ) < q := by
      qify at hq
      calc
        (n : ℚ) < (1006 + 1) / 1008 * q := h₂
        _ < (q : ℚ) := by linarith only [hq]
    -- Prove that n ≤ q - 2 by contradiction.
    have h₄ : n ≤ q - 2 := by
      by_contra!
      norm_cast at h₃ this
      -- Combine hypothesis h₃ to get n = q - 1.
      have h₄ : n = q - 1 := by omega
      -- Show that q > 1007.
      have h₅ : q > 1007 := by
        rw [h₄] at h₁
        field_simp at h₁
        rw [div_lt_iff₀] at h₁
        norm_cast at h₁
        rw [<-h₄, show (1006 * q : ℚ) = (1006 * q : ℤ) by simp] at h₁
        norm_cast at h₁
        omega
        norm_num
      -- Show that q < 1008 := by
      have h₆ : q < 1008 := by
        rw [h₄] at h₂
        field_simp at h₂
        rw [lt_div_iff₀] at h₂
        norm_num at h₂
        norm_cast at h₂
        linarith only [h₂]
        norm_num
      -- Contradiction sincce 1007 < q < 1008 is impossible.
      omega
    -- Show that q > 2014.
    qify at h₄
    have h₅ := h₁.trans_le h₄
    field_simp at h₅
    rw [div_lt_iff₀] at h₅
    norm_cast at h₅
    replace h₅ : q > 2014 := by
      rw [show (q - 2 : ℚ) = (q - 2 : ℤ) by simp] at h₄
      rw [show (1006 * q : ℚ) = (1006 * q : ℤ) by simp, show ((q - 2) * 1007 : ℚ) = ((q - 2) * 1007 : ℤ) by simp] at h₅
      norm_cast at h₄ h₅
      linarith only [h₅]
    -- Completing the proof to say that q = 2015 is the smallest.
    omega
    norm_num
