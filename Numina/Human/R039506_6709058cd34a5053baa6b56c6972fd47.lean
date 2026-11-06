import Mathlib

/- The expression $\sqrt{(\sqrt{56})(\sqrt{126})}$ can be simplified to $a\sqrt b$, where $a$ and $b$ are integers and $b$ is not divisible by any perfect square greater than 1. What is $a+b$? -/
theorem algebra_21184 {a b : ℕ}
    (h : √(√56 * √126) = a * √b) (hb : Squarefree b) : a + b = 23 := by
  -- We first simplify the expression
  -- $\sqrt{(\sqrt{56})(\sqrt{126})} = \sqrt{84}$
  have H : √(√56 * √126) = √84 :=
    calc _ = √√(56*126) := by rw [← Real.sqrt_mul (by norm_num)]
         _ = √√(84^2) := by norm_num
         _ = √84 := by simp
  rw [H] at h
  clear H

  -- Thus 84 = a^2 * b
  apply_fun (· ^ 2) at h
  ring_nf at h
  simp at h
  norm_cast at h

  -- Note: though we can get a = c, b = d from a^2 * b = c^2 * d if a, b, c, d are positive integers and b and d are squarefree, but it is difficult to prove this in Lean
  -- Instead, we just try all possible values of a and b

  -- a ≤ 9 by simple calculation
  have H : a ≤ 9 := by
    have k : b ≠ 0 := by
      rintro rfl
      contradiction
    replace k : b ≥ 1 := Nat.one_le_iff_ne_zero.2 k
    suffices _ : a < 10 by omega
    nlinarith

  -- And a^2 | 84
  have h2 : a ^ 2 ∣ 84 := Dvd.intro b h.symm

  -- Try a = 1, 2, ..., 9
  interval_cases a
  -- All the goals contradict h2 except for a = 1, 2
  all_goals
    try contradiction
  
  . -- If a = 1, then b = 84
    simp at h
    subst h
    -- 2^2 | 84, contradiction
    specialize hb 2
    simp at hb
    contradiction

  . -- If a = 2, then b = 21, and we are done
    obtain rfl : b = 21 := by omega
    simp
