import Mathlib

/- 11. Prove: For any real numbers $x, y, z$, the following three inequalities cannot all hold simultaneously: $|x|<|y-z|$, $|y|<|z-x|$, $|z|<|x-y|$. -/
theorem inequalities_223947 (x y z : ℝ) :
    ¬(|x| < |y - z| ∧ |y| < |z - x| ∧ |z| < |x - y|) := by
  -- we'll prove by contradiction
  by_contra h
  obtain ⟨h₁, h₂, h₃⟩ := h
  -- first prove that if |a| < |b-c| then by squaring and factoring (a + b-c) * (a-b+c) < 0
  have aux {a b c : ℝ} (h: |a| < |b-c|) : (a + b - c) * (a - b + c) < 0 := by
    have : a^2 < (b-c)^2 := by
      nth_rw 1 [← sq_abs]
      nth_rw 2 [← sq_abs]
      exact (sq_lt_sq₀ (by positivity) (by positivity)).mpr h
    ring_nf; ring_nf at this
    linarith
  -- we get 3 inequalities from last lemma, multiply them to get ((x-y+z) * (y-z+x) * (z-x+y))^2 < 0 which is impossible
  have h₁ := aux h₁
  have h₂ := aux h₂
  have h₃ := aux h₃
  clear * - h₁ h₂ h₃
  have h₄ := mul_pos_of_neg_of_neg h₁ h₂
  have h₅ := mul_neg_of_neg_of_pos h₃ h₄
  convert_to ((x-y+z) * (y-z+x) * (z-x+y))^2 < 0 at h₅
  . ring
  . linarith [sq_nonneg ((x-y+z) * (y-z+x) * (z-x+y))]