import Mathlib

/- Barry wrote 6 different numbers, one on each side of 3 cards, and laid the cards on a table, as shown. The sums of the two numbers on each of the three cards are equal. The three numbers on the hidden sides are prime numbers. What is the average of the hidden prime numbers? [asy]
path box=(0,0)--(1,0)--(1,1.5)--(0,1.5)--cycle;
draw(box);
draw(shift(1.5,0)*box);
draw(shift(3,0)*box);
label("44", (0.5, .75));
label("59", (2, .75));
label("38", (3.5, .75));
[/asy] -/

theorem algebra_13873 (a b c d e f : ℕ) (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : a ≠ d)
    (h₃ : a ≠ e) (h₄ : a ≠ f) (h₅ : b ≠ c) (h₆ : b ≠ d) (h₇ : b ≠ e) (h₈ : b ≠ f)
    (h₉ : c ≠ d) (h₁₀ : c ≠ e) (h₁₁ : c ≠ f) (h₁₂ : d ≠ e) (h₁₃ : d ≠ f) (h₁₄ : e ≠ f)
    (h₁₅ : a = 44) (h₁₆ : b = 59) (h₁₇ : c = 38) (h₁₈ : a + d = b + e)
    (h₁₉ : b + e = c + f) (h₂₀ : c + f = a + d) (h₂₁ : Nat.Prime d)
    (h₂₂ : Nat.Prime e) (h₂₃ : Nat.Prime f) :
    (d + e + f) / (3 : ℝ) = 14 := by
  -- We shall show that e must not be odd, and hence equals 2.
  have h₂₄ : e = 2 := by
    by_contra! h₂₄
    have h₂₅ : Odd e := Nat.Prime.odd_of_ne_two h₂₂ h₂₄
    replace h₂₅ : Even (b + e) := by
      apply Odd.add_odd
      rw [h₁₆]
      native_decide -- Prove that 59 is odd.
      exact h₂₅
    -- We have f = 2.
    have h₂₆ : Even (38 + f) := by
      rw [<-h₁₇, <-h₁₉]
      exact h₂₅
    have h₂₇ : Even f := by
      rw [show f = 38 + f - 38 by simp]
      rw [Nat.even_sub]
      simp [h₂₆]
      native_decide -- Prove that 38 is even.
      norm_num
    rw [Nat.Prime.even_iff h₂₃] at h₂₇
    -- We have d = 2 as well.
    have h₂₈ : Even (44 + d) := by
      rw [<-h₁₅, h₁₈]
      exact h₂₅
    have h₂₉ : Even d := by
      rw [show d = 44 + d - 44 by simp]
      rw [Nat.even_sub]
      simp [h₂₈]
      native_decide -- Prove that 38 is even.
      norm_num
    rw [Nat.Prime.even_iff h₂₁] at h₂₉
    -- We have d = f, contradicting h₁₃.
    rw [h₂₇, h₂₉] at h₁₃
    tauto
  -- Since e = 2, the other numbers can be solved immediately.
  rw [h₁₆, h₂₄] at h₁₈ h₁₉
  rw [h₁₅] at h₁₈
  rw [h₁₇] at h₁₉
  have h₂₅ : d = 17 := by
    omega
  have h₂₆ : f = 23 := by
    omega
  rw [h₂₄, h₂₅, h₂₆]
  norm_num