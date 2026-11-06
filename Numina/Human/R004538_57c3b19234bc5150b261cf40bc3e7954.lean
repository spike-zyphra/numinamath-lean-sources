import Mathlib


/- 1. On the board in the laboratory, two numbers are written. Every day, senior researcher Petya erases both numbers from the board and writes down their arithmetic mean and harmonic mean instead. On the morning of the first day, the numbers 1 and 2 were written on the board. Find the product of the numbers written on the board in the evening of the 1999th day. (The arithmetic mean of two numbers $a$ and $b$ is the number $\frac{a+b}{2}$, and the harmonic mean is the number $\frac{2}{1 / a+1 / b}$.) -/
theorem algebra_280831 {a : ℕ → ℝ × ℝ}
  (h0 : a 0 = (1, 2))
  (hn : ∀ n, a (n + 1) = (((a n).fst + (a n).snd) / 2, 2 / (1 / (a n).fst + 1 / (a n).snd)))
 :
    (a 1999).fst * (a 1999).snd = 2 := by
  -- we'll prove the fact for general k instead of 1999
  generalize 1999 = k
  -- we'll also prove along side that both of fst and snd of a k is positive
  suffices (a k).fst * (a k).snd = 2 ∧ (a k).fst > 0 ∧ (a k).snd > 0 by
    exact this.left
  -- now do induction
  induction' k with m hm
  . rw [h0]
    simp
    -- in inductive case, get formulas for fst and snd of a (m+1)
  . obtain ⟨hm₁, hm₂, hm₃⟩ := hm
    replace hn := hn m
    rw [← Prod.eta (a (m + 1)), Prod.mk.injEq] at hn
    have ⟨hn₁, hn₂⟩ := hn
    rw [hn₁, hn₂]
    -- now prove the 3 targets using algebraic manipulation
    and_intros
    . field_simp
      rw [hm₁]
      ring
    . positivity
    . positivity