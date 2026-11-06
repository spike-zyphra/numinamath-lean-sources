import Mathlib

/- 12. $[\mathbf{8}]$ Given that $62^{2}+122^{2}=18728$, find positive integers $(n, m)$ such that $n^{2}+m^{2}=9364$. -/
theorem number_theory_162925 (h: 62^2 + 122^2 = 18728):
  92^2 + 30^2 = 9364 := by
  have: 18728 = 2 * 9364 := by norm_num
  rw [this] at h
  -- if a^2 + b^2 = 2c, then ((a+b)/2)^2 + ((a-b)/2)^2 = c.

  replace {a b c: ℕ} (ha: Even a) (hb: Even b) (hab: a ≥ b)
    (heq: a^2 + b^2 = 2*c):
    ((a+b)/2)^2 + ((a-b)/2)^2 = c := by
    have h1: Even (a+b) := ha.add hb
    have h2: Even (a-b) := ha.tsub hb
    qify at heq ⊢
    rw [even_iff_two_dvd] at h1 h2
    zify at h1 h2
    rw [Nat.cast_sub hab] at h2
    rw [Nat.cast_sub hab, Int.cast_div h1 (by norm_num),
    Int.cast_div h2 (by norm_num)]
    replace heq: (c:ℚ) = (a^2+b^2) / 2 := by
      linarith only [heq]
    rw [heq]
    push_cast
    ring

  have h1: 92 = (122+62)/2 := by norm_num
  have h2: 30 = (122 - 62)/2 := by norm_num
  rw [add_comm] at h
  rw [h1, h2]
  apply this ?_ ?_ (by norm_num) h
  <;> exact Nat.even_iff.mpr rfl