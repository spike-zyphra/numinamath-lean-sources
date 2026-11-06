import Mathlib

/- 1.57 Prove that there do not exist integers $a, b, c, d$, such that the expression

$$

a x^{3}+b x^{2}+c x+d \text {, }

$$


when $x=19$, the value is 1, and when $x=62$, the value is 2.
(2nd All-Russian Mathematical Olympiad, 1962) -/
theorem algebra_292427 :
    ¬∃ a b c d : ℤ, (a * 19^3 + b * 19^2 + c * 19 + d = 1) ∧ (a * 62^3 + b * 62^2 + c * 62 + d = 2) := by
      by_contra h
      obtain ⟨a, b, c, d, h1, h2⟩ := h
      --Subtracting the two equations gives the following.
      have H1 : a * (62^3 - 19^3) + b * (62^2 - 19^2) + c * (62 - 19) = 1 := by linarith
      --Now we factor out a 43.
      have H2 : 43 * (a * (62^2 + 62 * 19 + 19^2) + b * (62 + 19) + c) = 1 := by linarith
      --This means 43 ∣ 1, which is clearly a contradiction.
      have H3 : 43 ∣ 1 := by omega
      omega